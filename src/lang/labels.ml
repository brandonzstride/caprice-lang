
module Variant = struct
  module T = struct
    type t = VariantLabel of Ident.t [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  let to_ident (VariantLabel id) = id
  let of_ident id = VariantLabel id

  let to_string (VariantLabel id) = "`" ^ Ident.to_string id

  include Utils.Set_map.Make_H (T)
end

module Record = struct
  module T = struct
    type t = RecordLabel of Ident.t [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  let to_ident (RecordLabel id) = id
  let of_ident id = RecordLabel id

  let to_string (RecordLabel id) = Ident.to_string id

  include Utils.Set_map.Make_H (T)
end
