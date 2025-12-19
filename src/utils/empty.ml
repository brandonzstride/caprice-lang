
type t = private | [@@deriving eq, ord]

let absurd : 'a. t -> 'a = function _ -> .
