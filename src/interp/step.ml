
type t = Step of int [@@unboxed]
  [@@deriving eq, ord]

let zero = Step 0

let[@inline always] next (Step i : t) : t =
  Step (i + 1)

let (>) (Step a) (Step b) = a > b

let uid (Step i) = i
