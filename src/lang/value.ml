
open Features

(*
  The `Atom_cell` is the payload of int and bool values.
  It is expected to be identity or a pair of concrete and
  symbolic components.
*)
module Make (Atom_cell : Utils.Comparable.S1) = struct
  type data = private Data [@@deriving eq, ord]
  type typeval = private Typeval [@@deriving eq, ord]

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
    | VFunClosure : { param : Ident.t ; closure : closure } -> data t
    | VVariant : any Variant.t -> data t
    | VRecord : any Record.t -> data t
    | VTuple : any * any -> data t
    | VFunFix : { fvar : Ident.t ; param : Ident.t ; closure : closure } -> data t (* no mutual recursion yet *)
    (* generated values *)
    | VGenFun : (typeval t, typeval t) Funtype.t -> data t
    | VGenPoly : { id : int ; nonce : int } -> data t
    (* type values only *)
    | VType : typeval t
    | VTypePoly : { id : int } -> typeval t
    | VTypeUnit : typeval t
    | VTypeTop : typeval t
    | VTypeBottom : typeval t
    | VTypeInt : typeval t
    | VTypeBool : typeval t
    | VTypeMu : { var : Ident.t ; closure : closure } -> typeval t
    | VTypeFun : (typeval t, typeval t) Funtype.t -> typeval t
    | VTypeRecord : typeval t Record.t -> typeval t
    | VTypeVariant : typeval t Labels.Variant.Map.t -> typeval t
    | VTypeRefine : (typeval t, closure) Refinement.t -> typeval t
    | VTypeTuple : typeval t * typeval t -> typeval t

  and closure = { body : Ast.t ; env : env }

  and env = any Env.t

  and any = Any : 'a t -> any [@@unboxed]

  module Env = Env.Make (struct type t = any end)

  type dval = data t
  type tval = typeval t

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
      | VTuple _
      | VFunFix _
      | VGenFun _
      | VGenPoly _) as x -> data x
    | ( VType
      | VTypePoly _
      | VTypeUnit 
      | VTypeTop
      | VTypeBottom
      | VTypeInt
      | VTypeBool
      | VTypeMu _
      | VTypeFun _
      | VTypeRecord _
      | VTypeVariant _
      | VTypeRefine _
      | VTypeTuple _) as x -> typeval x

  let[@inline always] handle_any (type a) (v : any) ~(data : data t -> a) ~(typeval : typeval t -> a) : a =
    map_any { f = handle ~data ~typeval } v

  module Match_result = struct
    type t =
      | Match
      | Match_bindings of env
      | No_match
  end

  let rec matches : type a. Pattern.t -> a t -> Match_result.t = fun p v ->
    match p, v with
    | _, VGenPoly _ -> No_match (* generated polymorphic values cannot be matched on *)
    | PAny, _ -> Match
    | PVariable id, v -> Match_bindings (Env.singleton id (to_any v))
    | PVariant { label = pattern_label ; payload = payload_pattern },
      VVariant { label = subject_label ; payload = Any v } ->
        if Labels.Variant.equal pattern_label subject_label
        then matches payload_pattern v
        else No_match
    | PTuple (p1, p2), VTuple (Any v1, Any v2) ->
      begin match matches p1 v1 with
      | Match -> matches p2 v2
      | Match_bindings e1 ->
        begin match matches p2 v2 with
        | Match -> Match_bindings e1
        | Match_bindings e2 -> Match_bindings (Env.extend e1 e2)
        | No_match -> No_match
        end
      | No_match -> No_match
      end
    | _ -> No_match

  let matches_any : Pattern.t -> any -> Match_result.t = fun pat a ->
    let f (type a) (v : a t) : Match_result.t =
      matches pat v
    in
    map_any { f } a

  (* Some setup to write intensional equality *)
  (* let rec equal : type a. a t -> a t -> bool = fun a b ->
    match a, b with
    | VUnit, VUnit
    | VInt, Vint
    | VBool, VBool
    | VFunClosure, VFunClosure
    | VVariant, VVariant
    | VRecord, VRecord
    | VTuple, VTuple
    | VFunFix, VFunFix
    (* generated values *)
    | VGenFun, VGenFun
    | VGenPoly, VGenPoly
    (* type values only *)
    | VType, VType
    | VTypePoly, VTypePoly
    | VTypeUnit, VTypeUnit
    | VTypeTop, VTypeTop
    | VTypeBottom, VTypeBottom
    | VTypeInt, VTypeInt
    | VTypeBool, VTypeBool
    | VTypeMu, VTypeMu
    | VTypeFun, VTypeFun
    | VTypeRecord, VTypeRecord
    | VTypeVariant, VTypeVariant
    | VTypeRefine, VTypeRefine
    | VTypeTuple, VTypeTuple -> failwith "need to do" *)
end

(*
  Ints and bools have only a concrete component.
*)
module Concrete = Make (Utils.Identity)

include Concrete
