
type t = Priority of int [@@unboxed]
  [@@deriving eq, ord]

let zero = Priority 0

let to_int (Priority n) = n

let geq (Priority n1) (Priority n2) = n1 >= n2

let[@inline always] plus_int (Priority n) i = 
  Priority (n + i)
