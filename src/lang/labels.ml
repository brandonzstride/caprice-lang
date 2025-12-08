
module Variant = struct
  module T = struct
    type t = VariantLabel of Ident.t [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  let to_ident (VariantLabel id) = id

  module Map = Baby.H.Map.Make (T)
end

module Record = struct
  module T = struct
    type t = RecordLabel of Ident.t [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  let to_ident (RecordLabel id) = id

  module Map = Baby.H.Map.Make (T)
end
