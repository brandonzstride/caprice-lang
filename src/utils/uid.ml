
module T = struct
  type t = Uid of int [@@unboxed]
    [@@deriving eq, ord]
end

include T

let of_int i = Uid i
let to_int (Uid i) = i

let counter = Counter.create ()

let make_new () = Uid (Counter.next counter)

module Map = Baby.H.Map.Make (T)
module Set = Baby.H.Set.Make (T)
