
module Q = Psq.Make (Target) (Int)

type k = Stepkey.t
type t = BFS of Q.t [@@unboxed]

let empty : t = BFS Q.empty

let push_one (BFS q : t) (target : Target.t) : t =
  let priority = Path_length.to_int (Target.path_length target) in
  BFS (Q.push target priority q)

let push_list (x : t) (ls : Target.t list) : t =
  List.fold_left push_one x ls

let remove (BFS q : t) (target : Target.t) : t =
  BFS (Q.remove target q)

let pop (BFS q : t) : (Target.t * t) option =
  match Q.pop q with
  | Some ((target, _), t) -> Some (target, BFS t)
  | None -> None

(* contains only the empty target *)
let initial : t =
  push_one empty Target.empty

