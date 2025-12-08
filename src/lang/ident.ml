
module T = struct
  type t = Ident of string [@@unboxed]
    [@@deriving eq, ord]
end

include T

module Map = Baby.H.Map.Make (T)
