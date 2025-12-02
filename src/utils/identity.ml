
type 'a t = 'a

let compare : ('a -> 'a -> int) -> ('a t -> 'a t -> int) = Fun.id
let equal : ('a -> 'a -> bool) -> ('a t -> 'a t -> bool) = Fun.id
