
type data
type typeval

type _ t =
  (* non-type value *)
  | VUnit : data t
  | VInt : int -> data t
  | VBool : bool -> data t
  | VFunClosure : { var : Ident.t ; body : closure } -> data t
  | VVariant : { label : Labels.Variant.t ; payload : any } -> data t
  | VRecord : any Labels.Record.Map.t -> data t
  | VFunFix : { fvar : Ident.t ; param : Ident.t ; closure : closure } -> data t (* no mutual recursion yet *)
  (* generated values *)
  | VGenFun : { domain : typeval t ; codomain : typeval t } -> data t
  | VGenPoly : { id : int ; nonce : int } -> data t
  (* type values only *)
  | VType : typeval t
  | VTypePoly : { id : int } -> typeval t
  | VTypeUnit : typeval t
  | VTypeBottom : typeval t
  | VTypeInt : typeval t
  | VTypeBool : typeval t
  | VTypeMu : { var : Ident.t ; closure : closure } -> typeval t
  | VTypeFun : { domain : typeval t ; codomain : typeval t } -> typeval t
  | VTypeRecord : typeval t Labels.Record.Map.t -> typeval t
  | VTypeRefine : { var : Ident.t ; tval : typeval t ; predicate : closure } -> typeval t

and closure = { body : Ast.t ; env : env }

and env = any Ident.Map.t

and any = Any : 'a t -> any [@@unboxed]

let[@inline always] to_any : type a. a t -> any = fun v -> Any v

let[@inline always] handle (type a b) (v : a t) ~(data : data t -> b) ~(typeval : typeval t -> b) : b =
  match v with
  | ( VUnit
    | VInt _
    | VBool _
    | VFunClosure _
    | VVariant _
    | VRecord _
    | VFunFix _
    | VGenFun _
    | VGenPoly _) as x -> data x
  | ( VType
    | VTypePoly _
    | VTypeUnit 
    | VTypeBottom
    | VTypeInt
    | VTypeBool
    | VTypeMu _
    | VTypeFun _
    | VTypeRecord _
    | VTypeRefine _) as x -> typeval x
