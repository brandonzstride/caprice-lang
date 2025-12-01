
module Variant = struct
  module T = struct
    type t = VariantLabel of Ident.t
      [@@deriving eq, ord]
  end

  include T

  module Map = Baby.H.Map.Make (T)
end

module Record = struct
  module T = struct
    type t = RecordLabel of Ident.t
      [@@deriving eq, ord]
  end

  include T

  module Map = Baby.H.Map.Make (T)
end
