
module Variant = struct
  type t = VariantLabel of Ident.t
end

module Record = struct
  type t = RecordLabel of Ident.t
end
