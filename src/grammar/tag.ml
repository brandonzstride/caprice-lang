
type reason =
  | GenList             (* generate empty or cons *)
  | CheckList           (* check hd or tl *)
  | CheckTuple          (* check left or right side of tuple *)
  | CheckSingletype     (* check subset or superset *)
  | CheckGenFun         (* check domain or codomain *)
  | CheckWrappedFun     (* check domain or codomain of a wrapped function *)
  | CheckRefinementType (* check underlying type or evaluate the predicate *)
  | CheckLetExpr        (* type check a let-expression, or eval body *)
  | ApplGenFun          (* type check argument, or generate result *)
  | ApplWrappedFun      (* type check argument, or evaluate body *)
  [@@deriving eq, ord]

let reason_to_string = function
  | GenList             -> "Generate list"
  | CheckList           -> "Check list"
  | CheckTuple          -> "Check tuple"
  | CheckSingletype     -> "Check singletype"
  | CheckGenFun         -> "Check generated function"
  | CheckWrappedFun     -> "Check wrapped function"
  | CheckRefinementType -> "Check refinement type"
  | CheckLetExpr        -> "Check let-expression"
  | ApplGenFun          -> "Apply generated function"
  | ApplWrappedFun      -> "Apply wrapped function"

type dir =
  | Gen   (* the label is used to generate something *)
  | Check (* the label is used to check something *)
  [@@deriving eq, ord, show]

module T = struct
  type t =
    | Left of reason
    | Right of reason
    | Label of Lang.Ident.t * dir
    [@@deriving eq, ord]

  let of_variant_label dir vlabel =
    Label (Lang.Labels.Variant.to_ident vlabel, dir)

  let of_record_label dir rlabel =
    Label (Lang.Labels.Record.to_ident rlabel, dir)
end

include T

let priority = function
  | Label (_, Gen) -> 1
  | Label (_, Check) -> 0
  | (Left reason | Right reason) ->
    match reason with
    | GenList -> 1
    | _ -> 0

let to_string = function
  | Left reason -> Format.sprintf "Left (%s)" (reason_to_string reason)
  | Right reason -> Format.sprintf "Right (%s)" (reason_to_string reason)
  | Label (Ident s, dir) -> Format.sprintf "%s (%s)" s (show_dir dir)

(* Tags with alternatives *)
module With_alt = struct
  type t = { main : T.t ; alts : T.t list }
    [@@deriving eq, ord]
end
