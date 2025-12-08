
type t =
  | IBool of bool
  | IInt of int
  | ILabel of Label.t
  [@@deriving eq, ord]

let bool_opt = function
  | IBool b -> Some b
  | _ -> None

let int_opt = function
  | IInt i -> Some i
  | _ -> None

let label_opt = function
  | ILabel l -> Some l
  | _ -> None
