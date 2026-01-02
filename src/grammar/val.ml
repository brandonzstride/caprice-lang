
open Lang

include Value.Make (Cdata)

(* 
  True if the value has any non-constant symbolic formula in it.

  This is used to see if recursive functions are called with symbolic
  values when type splaying.
*)
let rec is_symbolic : type a. a t -> bool = fun v ->
  match v with
  | VUnit
  | VGenPoly _
  | VEmptyList
  | VType
  | VTypePoly _
  | VTypeUnit
  | VTypeTop
  | VTypeBottom
  | VTypeInt
  | VTypeBool -> false
  | VInt (_, s) -> not (Smt.Formula.is_const s)
  | VBool (_, s) -> not (Smt.Formula.is_const s)
  (* Recursive cases: is symbolic if any subvalue is *)
  | VVariant { payload = Any v' ; label = _ } -> is_symbolic v'
  | VModule map_body
  | VRecord map_body ->
    Labels.Record.Map.exists (fun _ (Any v') -> is_symbolic v') map_body
  | VTuple (Any v1, Any v2) ->
    is_symbolic v1 || is_symbolic v2
  | VListCons (Any v_hd, v_tl) ->
    is_symbolic v_hd || is_symbolic v_tl
  | VTypeList t ->
    is_symbolic t
  | VTypeRecord record_body ->
    Labels.Record.Map.exists (fun _ t -> is_symbolic t) record_body
  | VTypeVariant variant_body ->
    Labels.Variant.Map.exists (fun _ t -> is_symbolic t) variant_body
  | VTypeTuple (t1, t2) ->
    is_symbolic t1 || is_symbolic t2
  | VTypeSingle t ->
    is_symbolic t
  | VTypeFun { domain ; codomain = CodValue t }
  | VGenFun { domain ; codomain = CodValue t } ->
    is_symbolic domain || is_symbolic t
  | VWrapped { data ; tau = { domain ; codomain = CodValue t } } ->
    is_symbolic data || is_symbolic domain || is_symbolic t
  (* Closures cases: assume true, but may want to inspect closure *)
  | VFunClosure _
  | VFunFix _
  | VTypeModule _
  | VLazy _
  | VTypeMu _
  | VTypeRefine _
  | VGenFun { domain = _ ; codomain = CodDependent _ }
  | VTypeFun { domain = _ ; codomain = CodDependent _ }
  | VWrapped { data = _ ; tau = { domain = _ ; codomain = CodDependent _ } } -> true

let is_any_symbolic (Any v) = is_symbolic v
