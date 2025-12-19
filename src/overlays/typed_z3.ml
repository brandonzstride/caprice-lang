
open Smt

module type CONTEXT = sig
  val ctx : Z3.context
end

(*
  Z3 expressions using some context.
*)
module Make_of_context (C : CONTEXT) : Formula.SOLVABLE = struct
  (* I'm relying on internal correctness, and the types are phantom *)
  type ('a, 'k) t = Z3.Expr.expr

  let ctx = C.ctx

  let equal = Z3.Expr.equal

  let const_int (i : int) : (int, 'k) t = Z3.Arithmetic.Integer.mk_numeral_i ctx i
  let const_bool (b : bool) : (bool, 'k) t = Z3.Boolean.mk_val ctx b

  let zero = const_int 0
  let one = const_int 1

  let intS = Z3.Arithmetic.Integer.mk_sort ctx
  let boolS = Z3.Boolean.mk_sort ctx

  let mk_symbol sort uid =
    Z3.Expr.mk_const ctx (Z3.Symbol.mk_int ctx (Utils.Uid.to_int uid)) sort

  let symbol (type a) (s : (a, 'k) Symbol.t) : (a, 'k) t =
    match s with
    | I k -> mk_symbol intS k
    | B k -> mk_symbol boolS k

  let not_ (e : (bool, 'k) t) : (bool, 'k) t =
    Z3.Boolean.mk_not ctx e

  let list_curry f x y = f [ x ; y ]

  let divides a b =
    Z3.Boolean.mk_eq ctx (const_int 0) (Z3.Arithmetic.Integer.mk_mod ctx b a)

  let rec binop : type a b. (a * a * b) Binop.t -> (a, 'k) t -> (a, 'k) t -> (b, 'k) t = function
    | Plus            -> list_curry @@ Z3.Arithmetic.mk_add ctx
    | Minus           -> list_curry @@ Z3.Arithmetic.mk_sub ctx
    | Times           -> list_curry @@ Z3.Arithmetic.mk_mul ctx
    | Less_than       -> Z3.Arithmetic.mk_lt ctx
    | Less_than_eq    -> Z3.Arithmetic.mk_le ctx
    | Greater_than    -> Z3.Arithmetic.mk_gt ctx
    | Greater_than_eq -> Z3.Arithmetic.mk_ge ctx
    | Equal           -> Z3.Boolean.mk_eq ctx
    | Not_equal       -> fun a b -> not_ (Z3.Boolean.mk_eq ctx a b)
    | Or              -> list_curry @@ Z3.Boolean.mk_or ctx
    (* OCaml division and modulus differ from Z3, so we need some extra encoding *)
    | Divide -> fun x y ->
      let div = Z3.Arithmetic.mk_div ctx x y in
      Z3.Boolean.mk_ite ctx
        (binop Or (divides y x) (binop Less_than_eq zero x))
        div
        (Z3.Boolean.mk_ite ctx
          (binop Less_than_eq zero y)
          (binop Plus div one)
          (binop Minus div one)
      )
    | Modulus -> fun x y ->
      binop Minus x (binop Times y (binop Divide x y))

  let is_const (type a) (x : (a, 'k) t) : bool =
    Z3.Expr.is_const x

  let and_ (exprs : (bool, 'k) t list) : (bool, 'k) t =
    Z3.Boolean.mk_and ctx exprs

  let solver = Z3.Solver.mk_simple_solver ctx

  let unbox_int_expr e =
    if Z3.Expr.is_numeral e 
    then
      Z3.Arithmetic.Integer.get_big_int e
      |> Big_int_Z.int_of_big_int
      |> Option.some
    else None

  let unbox_bool_expr e =
    if Z3.Boolean.is_bool e
    then
      match Z3.Boolean.get_bool_value e with
      | L_FALSE -> Some false
      | L_TRUE -> Some true
      | L_UNDEF -> failwith "Invariant failure: undefined bool."
   else None

  let a_of_expr z3_model expr unbox_expr =
    Option.bind (Z3.Model.get_const_interp_e z3_model expr) unbox_expr

  let solve (exprs : (bool, 'k) t list) : 'k Solution.t =
    let e = and_ exprs in
    if Z3.Expr.equal e (const_bool false)
    then Unsat
    else begin
      (* Must use the solver stack in order to not keep decls around from previous solves *)
      (* (and this is faster than making a new solver) *)
      Z3.Solver.push solver;
      let result = Z3.Solver.check solver [ e ] in
      let solution =
        match result with
        | Z3.Solver.SATISFIABLE ->
          let model = Option.get @@ Z3.Solver.get_model solver in
          let value : type a. (a, 'k) Symbol.t -> a option = fun s ->
            match s with
            | I _ -> a_of_expr model (symbol s) unbox_int_expr
            | B _ -> a_of_expr model (symbol s) unbox_bool_expr
          in
          let domain = 
            List.map (fun decl ->
              decl
              |> Z3.FuncDecl.get_name
              |> Z3.Symbol.get_int
              |> Utils.Uid.of_int
            ) (Z3.Model.get_const_decls model)
          in
          Solution.Sat { value ; domain }
        | UNKNOWN -> Unknown
        | UNSATISFIABLE -> Unsat
      in
      Z3.Solver.pop solver 1;
      solution
    end
end

module Make () = Make_of_context (struct let ctx = Z3.mk_context [] end)

module Default = Make ()

include Default
