
type t =
  | PAny
  | PVariable of Ident.t
  | PVariant of { label : Labels.Variant.t ; payload_id : Ident.t }
  (* Will add lists, too *)
