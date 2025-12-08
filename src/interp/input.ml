
type t =
  | IBool of bool
  | IInt of int
  | ILabel of Label.t
  [@@deriving eq, ord]
