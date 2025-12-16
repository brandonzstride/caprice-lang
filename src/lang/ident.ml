
module T = struct
  type t = Ident of string [@@unboxed]
    [@@deriving eq, ord]
end

include T

let to_string (Ident s) = s

module Map = Baby.H.Map.Make (T)
