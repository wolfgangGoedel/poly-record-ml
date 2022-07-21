module Syntax = struct
  type name = Name of string | Int of int
  type constant = { name : name; constr : bool; arity : int }
  type var = string

  type expr =
    | Var of var
    | Const of constant
    | Fun of var * expr
    | App of expr * expr
    | Let of var * expr * expr

  let plus = Const { name = Name "+"; arity = 2; constr = false }
  let times = Const { name = Name "*"; arity = 2; constr = false }
  let int n = Const { name = Int n; arity = 0; constr = true }
end

open Syntax

module Reduce = struct
  let rec evaluated = function
    | Fun (_, _) -> true
    | u -> partial_application 0 u

  and partial_application n = function
    | Const c -> c.constr || c.arity > n
    | App (u, v) -> evaluated v && partial_application (n + 1) u
    | _ -> false

  exception Reduce

  let delta_bin_arith op code = function
    | App
        ( App ((Const { name = Name _; arity = 2 } as c), Const { name = Int x }),
          Const { name = Int y } )
      when c = op ->
        int (code x y)
    | _ -> raise Reduce

  let delta_plus = delta_bin_arith plus ( + )
  let delta_times = delta_bin_arith times ( * )
  let delta_rules = [ delta_plus; delta_times ]
  let union f g a = try g a with Reduce -> f a
  let delta = List.fold_right union delta_rules (fun _ -> raise Reduce)

  let rec subst x v a =
    assert (evaluated v);
    match a with
    | Var y -> if x = y then v else a
    | Fun (y, a') -> if x = y then a else Fun (y, subst x v a')
    | App (a', a'') -> App (subst x v a', subst x v a'')
    | Let (y, a', a'') ->
        Let (y, subst x v a', if x = y then a'' else subst x v a'')
    | Const c -> Const c

  let beta = function
    | App (Fun (x, a), v) when evaluated v -> subst x v a
    | Let (x, v, a) when evaluated v -> subst x v a
    | _ -> raise Reduce

  let top_reduction = union beta delta

  let rec eval =
    let eval_top_reduce a = try eval (top_reduction a) with Reduce -> a in
    function
    | App (a1, a2) ->
        let v1 = eval a1 in
        let v2 = eval a2 in
        eval_top_reduce (App (v1, v2))
    | Let (x, a1, a2) ->
        let v1 = eval a1 in
        eval_top_reduce (Let (x, v1, a2))
    | a -> eval_top_reduce a
end

module BigStep = struct
  type env = (string * value) list
  and value = Closure of var * expr * env | Constant of constant * value list

  type answer = Error | Value of value

  let val_int u =
    Value (Constant ({ name = Int u; arity = 0; constr = true }, []))

  let delta c l =
    match (c.name, l) with
    | ( Name "+",
        [ Constant ({ name = Int u }, []); Constant ({ name = Int v }, []) ] )
      ->
        val_int (u + v)
    | ( Name "*",
        [ Constant ({ name = Int u }, []); Constant ({ name = Int v }, []) ] )
      ->
        val_int (u * v)
    | _ -> Error

  let get x env = try Value (List.assoc x env) with Not_found -> Error

  let rec eval env = function
    | Var x -> get x env
    | Const c -> Value (Constant (c, []))
    | Fun (x, a) -> Value (Closure (x, a, env))
    | Let (x, a1, a2) -> (
        match eval env a1 with
        | Value v1 -> eval ((x, v1) :: env) a2
        | Error -> Error)
    | App (a1, a2) -> (
        match eval env a1 with
        | Value v1 -> (
            match (v1, eval env a2) with
            | Constant (c, l), Value v2 ->
                let k = List.length l + 1 in
                if c.arity < k then Error
                else if c.arity > k then Value (Constant (c, v2 :: l))
                else if c.constr then Value (Constant (c, v2 :: l))
                else delta c (v2 :: l)
            | Closure (x, e, env0), Value v2 -> eval ((x, v2) :: env0) e
            | _, Error -> Error)
        | Error -> Error)
end

module Unify = struct
  type type_symbol = Tarrow | Tint

  type texp = { mutable texp : node; mutable mark : int }
  and node = Desc of desc | Link of texp
  and desc = Tvar of int | Tcon of type_symbol * texp list

  type scheme = texp list * texp

  let texp d = { texp = Desc d; mark = 0 }

  let tvar () =
    let count = ref 0 in
    fun () ->
      incr count;
      texp (Tvar !count)

  let tvar = tvar ()
  let tint = texp (Tcon (Tint, []))
  let tarrow t1 t2 = texp (Tcon (Tarrow, [ t1; t2 ]))
  let last_mark = ref 0

  let marker () =
    incr last_mark;
    !last_mark

  let rec repr t =
    match t.texp with
    | Link u ->
        let v = repr u in
        t.texp <- Link v;
        v
    | Desc _ -> t

  let desc t = match (repr t).texp with Link _ -> assert false | Desc d -> d

  exception Unify of texp * texp
  (* exception Arity of texp * texp *)

  let link t1 t2 = (repr t1).texp <- Link t2

  let rec unify t1 t2 =
    let t1 = repr t1 and t2 = repr t2 in
    if t1 == t2 then ()
    else
      match (desc t1, desc t2) with
      | Tvar _, _ -> link t1 t2
      | _, Tvar _ -> link t2 t1
      | Tcon (g1, l1), Tcon (g2, l2) when g1 = g2 ->
          link t1 t2;
          List.iter2 unify l1 l2
      | _, _ -> raise (Unify (t1, t2))

  exception Cycle of texp list

  let acyclic t =
    let visiting = marker () and visited = marker () in
    let cycles = ref [] in
    let rec visit t =
      let t = repr t in
      if t.mark > visiting then ()
      else if t.mark = visiting then cycles := t :: !cycles
      else (
        t.mark <- visiting;
        (match desc t with Tvar _ -> () | Tcon (g, l) -> List.iter visit l);
        t.mark <- visited)
    in
    visit t;
    if !cycles <> [] then raise (Cycle !cycles)

  let funify t1 t2 =
    unify t1 t2;
    acyclic t1
end

module Infer = struct
  open Unify

  exception Undefined_constant of string

  let type_of_const c : scheme =
    let int3 = tarrow tint (tarrow tint tint) in
    match c.name with
    | Int _ -> ([], tint)
    | Name ("+" | "*") -> ([], int3)
    | Name n -> raise (Undefined_constant n)

  exception Free_variable of var

  let type_of_var tenv x =
    try List.assoc x tenv with Not_found -> raise (Free_variable x)

  let extend tenv (x, t) = (x, t) :: tenv

  let type_instance (q, t) =
    acyclic t;
    let copied =
      let copy t =
        let t = repr t in
        (t, tvar ())
      in
      List.map copy q
    in
    let rec visit t =
      let t = repr t in
      try List.assq t copied
      with Not_found -> (
        match desc t with
        | Tvar _ | Tcon (_, []) -> t
        | Tcon (g, l) -> texp (Tcon (g, List.map visit l)))
    in
    visit t

  let visit_type exclude visited f t =
    let rec visit t =
      let t = repr t in
      if t.mark = exclude || t.mark = visited then ()
      else (
        t.mark <- visited;
        f t;
        match desc t with Tvar _ -> () | Tcon (g, l) -> List.iter visit l)
    in
    visit t

  let generalizable tenv t0 =
    let inenv = marker () in
    let mark m t = (repr t).mark <- m in
    let visit_asumption (x, (q, t)) =
      let bound = marker () in
      List.iter (mark bound) q;
      visit_type bound inenv ignore t
    in
    List.iter visit_asumption tenv;
    let ftv = ref [] in
    let collect t = match desc t with Tvar _ -> ftv := t :: !ftv | _ -> () in
    let free = marker () in
    visit_type inenv free collect t0;

    !ftv

  let rec infer tenv a t =
    match a with
    | Const c -> funify (type_instance (type_of_const c)) t
    | Var x -> funify (type_instance (type_of_var tenv x)) t
    | Fun (x, a) ->
        let tv1 = tvar () and tv2 = tvar () in
        infer (extend tenv (x, ([], tv1))) a tv2;
        funify t (tarrow tv1 tv2)
    | App (a1, a2) ->
        let tv = tvar () in
        infer tenv a1 (tarrow tv t);
        infer tenv a2 tv
    | Let (x, a1, a2) ->
        let tv = tvar () in
        infer tenv a1 tv;
        let s = (generalizable tenv tv, tv) in
        infer (extend tenv (x, s)) a2 t

  let type_of a =
    let tv = tvar () in
    infer [] a tv;
    tv
end

let plus_x n = App (App (plus, Var "x"), n)

let e =
  App
    ( Fun ("x", App (App (times, plus_x (int 1)), plus_x (int (-1)))),
      App (Fun ("x", plus_x (int 1)), int 2) )
