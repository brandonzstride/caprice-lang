
open Features

(*
  The `Atom_cell` is the payload of int and bool values.
  It is expected to be identity or a pair of concrete and
  symbolic components.
*)
module Make (Atom_cell : Utils.Comparable.S1) = struct
  type data
  type typeval

  (*
    Data values and type values are all the same type constructor
    so that they are flat, and there is no pointer indirection.
    We can pack them into the same type in an unboxed way. This way,
    the representation is as if they are all just one type.
  *)
  type _ t =
    (* non-type value *)
    | VUnit : data t
    | VInt : int Atom_cell.t -> data t
    | VBool : bool Atom_cell.t -> data t
    | VFunClosure : { param : Ident.t ; body : closure } -> data t
    | VVariant : any Variant.t -> data t
    | VRecord : any Record.t -> data t
    | VFunFix : { fvar : Ident.t ; param : Ident.t ; closure : closure } -> data t (* no mutual recursion yet *)
    (* generated values *)
    | VGenFun : (typeval t, typeval t) Funtype.t -> data t
    | VGenPoly : { id : int ; nonce : int } -> data t
    (* type values only *)
    | VType : typeval t
    | VTypePoly : { id : int } -> typeval t
    | VTypeUnit : typeval t
    | VTypeBottom : typeval t
    | VTypeInt : typeval t
    | VTypeBool : typeval t
    | VTypeMu : { var : Ident.t ; closure : closure } -> typeval t
    | VTypeFun : (typeval t, typeval t) Funtype.t -> typeval t
    | VTypeRecord : typeval t Record.t -> typeval t
    | VTypeVariant : typeval t Variant.t list -> typeval t
    | VTypeRefine : (typeval t, closure) Refinement.t -> typeval t

  and closure = { body : Ast.t ; env : env }

  and env = any Env.t

  and any = Any : 'a t -> any [@@unboxed]

  let[@inline always] to_any : type a. a t -> any = fun v -> Any v

  type 'b f = { f : 'a. 'a t -> 'b } [@@unboxed]

  let[@inline always] map_any : 'a f -> any -> 'a = fun f (Any v) -> f.f v

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
      | VTypeVariant _
      | VTypeRefine _) as x -> typeval x

  module Match_result = struct
    type t =
      | Match
      | Match_bindings of env
      | No_match
  end

  let rec matches : type a. a t -> Pattern.t -> Match_result.t = fun v p ->
    match p, v with
    | _, VGenPoly _ -> No_match (* generated polymorphic values cannot be matched on *)
    | PAny, _ -> Match
    | PVariable id, v -> Match_bindings (Env.singleton id (to_any v))
    | PVariant { label = pattern_label ; payload = payload_pattern },
      VVariant { label = subject_label ; payload = Any v } ->
        if Labels.Variant.equal pattern_label subject_label
        then matches v payload_pattern
        else No_match
    | _ -> No_match
end

(*
  Ints and bools have only a concrete component.
*)
module Concrete = Make (Utils.Identity)

include Concrete
