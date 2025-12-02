
type 'a t = { label : Labels.Variant.t ; payload : 'a }
  [@@deriving eq, ord]
