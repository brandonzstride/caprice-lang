
type 'a t = 'a Labels.Record.Map.t
  [@@deriving eq, ord]

let empty = Labels.Record.Map.empty

module Parsing = struct
  let add_entry (k, v) = Labels.Record.Map.add k v

  let singleton (k, v) = Labels.Record.Map.singleton k v
end
