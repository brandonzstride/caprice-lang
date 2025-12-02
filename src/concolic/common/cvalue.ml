
module Make (K : Smt.Symbol.KEY) = struct
  include Lang.Value.Make (Cdata.Make (K))
end