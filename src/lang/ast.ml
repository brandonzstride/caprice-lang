
type t = 
  | EUnit
  | EInt of int
  | EBool of bool
  | EVar of Ident.t
  | EBinop of { left : t ; binop : Binop.t ; right : t }
  | EIf of { if_ : t ; then_ : t ; else_ : t }
  | ELet of { var : var ; defn : t ; body : t }
  | ELetRec of { var : var ; param : Ident.t ; defn : t ; body : t } (* no mutual recursion yet *)
  | EAppl of { func : t ; arg : t }
  | EMatch of { subject : t ; patterns : (Pattern.t * t) list }
  | EProject of { record : t ; label : Labels.Record.t }
  | ERecord of t Record.t
  | ETuple of t * t
  | EEmptyList
  | EListCons of t * t
  | EModule of statement list
  | ENot of t
  | EPick_i
  | EFunction of { param : Ident.t ; body : t }
  | EVariant of t Variant.t
  | EAssert of t
  | EAssume of t
  | EAbstractType (* evaluates to an abstract type *)
  (* Types *)
  | EType
  | ETypeInt
  | ETypeBool
  | ETypeTop
  | ETypeBottom
  | ETypeUnit
  | ETypeRecord of t Record.t
  | ETypeModule of Labels.Record.t typed_item list
  | ETypeFun of (fun_domain, t) Funtype.t
  | ETypeRefine of (t, t) Refinement.t
  | ETypeMu of { var : Ident.t ; body : t }
  | ETypeList of t
  | ETypeVariant of t Variant.t list
  | ETypeSingle of t
  [@@deriving eq, ord]

and var =
  | VarUntyped of { name : Ident.t }
  | VarTyped of Ident.t typed_item

and 'a typed_item = { item : 'a ; tau : t }

and fun_domain =
  | PReg of { tau : t } (* regular parameter *)
  | PDep of Ident.t typed_item (* dependent parameter *)

and statement =
  | SLet of { var : var ; defn : t }
  | SLetRec of { var : var ; param : Ident.t ; defn : t }
  [@@deriving eq, ord]

type program = statement list

let statement_to_t (stmt : statement) (body : t) : t =
  match stmt with
  | SLet { var ; defn } ->
    ELet { var ; defn ; body }
  | SLetRec { var ; param ; defn } ->
    ELetRec { var ; param ; defn ; body }

let rec t_of_statement_list (ls : statement list) : t =
  match ls with
  | [] -> EUnit
  | hd :: tl -> statement_to_t hd (t_of_statement_list tl)

let id_of_var (var : var) : Ident.t =
  match var with
  | VarUntyped { name } -> name
  | VarTyped { item ; tau = _ } -> item
