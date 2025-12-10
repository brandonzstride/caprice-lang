
type t =
  | Unknown          (* solver timeout *)
  | Exhausted_pruned (* no more targets up to some depth *)
  | Exhausted        (* completely ran all possible paths *)
  | Error            (* found an error *)
  [@@deriving eq, ord]
  (* comparison follows the listed ordering *)

let min a b =
  if compare a b < 0 then a else b
