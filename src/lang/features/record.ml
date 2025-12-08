
type 'a t = 'a Labels.Record.Map.t
  [@@deriving eq, ord]

let empty = Labels.Record.Map.empty

let fold (f : Labels.Record.t -> 'a -> 'acc -> 'acc) (acc : 'acc) (x : 'a t) : 'acc =
  Labels.Record.Map.fold f x acc

module Parsing = struct
  let add_entry (k, v) = Labels.Record.Map.add k v

  let singleton (k, v) = Labels.Record.Map.singleton k v
end
