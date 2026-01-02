
type t = Len of int [@@unboxed]
  [@@deriving eq, ord]

let zero = Len 0

let to_int (Len n) = n

let geq (Len n1) (Len n2) = n1 >= n2

let[@inline always] plus_int (Len n) i = Len (n + i)
