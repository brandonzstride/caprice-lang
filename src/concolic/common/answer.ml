
type t =
  | Found_error of string (* found an error *)
  | Unknown               (* solver timeout *)
  | Exhausted_pruned      (* no more targets up to some depth *)
  | Exhausted             (* completely ran all possible paths *)
  [@@deriving eq, ord]
  (* comparison follows the listed ordering *)

let min =
  function
  | Exhausted -> fun b -> b (* CPS *)
  | a -> fun b -> 
    if compare a b < 0 then a else b

let to_string = function
  | Found_error msg  -> "Found error: " ^ msg
  | Unknown          -> "Unknown"
  | Exhausted_pruned -> "Exausted pruned tree"
  | Exhausted        -> "Exhausted"

let is_signal_to_stop = function
  (* If we found an error, then we don't want to do any more runs *)
  | Found_error _ -> true
  (* ... otherwise, we still should try to pop another target *)
  | _ -> false
