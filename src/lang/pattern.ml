
type t =
  | PAny
  | PVariable of Ident.t
  | PVariant of t Features.Variant.t (* payload is another pattern *)
  (* Will add lists, too *)
  [@@deriving eq, ord]
