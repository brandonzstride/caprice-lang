
type t =
  | PAny
  | PVariable of Ident.t
  | PVariant of t Variant.t (* payload is a pattern *)
  | PTuple of t * t
  | PEmptyList
  | PDestructList of t * t
  [@@deriving eq, ord]
