
type t =
  | PAny
  | PVariable of Ident.t
  | PVariant of t Features.Variant.t (* payload is another pattern *)
  | PTuple of t * t
  (* Will add lists, too *)
  [@@deriving eq, ord]
