
type t =
  | Unknown
  | Ok
  | Error
  [@@deriving eq, ord]
  (* comparison follows the listed ordering *)
