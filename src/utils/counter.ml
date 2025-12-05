
module C = Safe_cell.Make (Int)

type t = C.t
let create () = C.create 0

let next (t : t) : int = C.update ((+) 1) t