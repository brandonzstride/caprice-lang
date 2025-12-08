
module Variant = struct
  module T = struct
    type t = VariantLabel of Ident.t [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  let to_ident (VariantLabel id) = id
  let of_ident id = VariantLabel id

  module B = Baby.H.Make (T)
  module Map = B.Map
  module Set = B.Set
end

module Record = struct
  module T = struct
    type t = RecordLabel of Ident.t [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  let to_ident (RecordLabel id) = id
  let of_ident id = RecordLabel id

  module B = Baby.H.Make (T)
  module Map = B.Map
  module Set = B.Set
end
