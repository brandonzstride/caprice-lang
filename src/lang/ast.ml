
type t = 
  | EUnit
  | EInt of int
  | EBool of bool
  | EVar of Ident.t
  | EBinop of { left : t ; binop : Binop.t ; right : t }
  | EIf of { if_ : t ; then_ : t ; else_ : t }
  | ELet of Ident.t let_expr
  | ELetTyped of typed_var let_expr
  | ELetRec of Ident.t let_expr (* no mutual recursion yet *)
  | ELetRecTyped of typed_var let_expr
  | EAppl of { func : t ; arg : t }
  | EMatch of { subject : t ; patterns : (Pattern.t * t) list }
  | EProject of { record : t ; label : Labels.Record.t }
  | ERecord of t Record.t
  | ETuple of t * t
  (* | EModule *)
  | ENot of t
  | EPick_i
  | EFunction of { param : Ident.t ; body : t }
  | EVariant of t Variant.t
  | EAssert of t
  | EAssume of t
  (* Types *)
  | EType
  | ETypeInt
  | ETypeBool
  | ETypeTop
  | ETypeBottom
  | ETypeUnit
  | ETypeRecord of t Record.t
  (* | ETypeModule *)
  | ETypeFun of (t, t) Funtype.t
  | ETypeRefine of (t, t) Refinement.t
  | ETypeMu of { var : Ident.t ; body : t }
  | ETypeVariant of t Variant.t list
  (* | ETypeSingle *)
  [@@deriving eq, ord]

and typed_var = { var : Ident.t ; tau : t }
  [@@deriving eq, ord]

and 'a let_expr = { var : 'a ; defn : t ; body : t }
  [@@deriving eq, ord]

and statement =
  | SUntyped of { var : Ident.t ; defn : t }
  | STyped of { var : Ident.t ; tau : t ; defn : t }
  [@@deriving eq, ord]

let statement_to_t (stmt : statement) (body : t) : t =
  match stmt with
  | SUntyped { var ; defn } ->
    ELet { var ; defn ; body }
  | STyped { var ; tau ; defn } ->
    ELetTyped { var = { var ; tau } ; defn ; body }

let rec t_of_statement_list (ls : statement list) : t =
  match ls with
  | [] -> EUnit
  | hd :: tl -> statement_to_t hd (t_of_statement_list tl)
