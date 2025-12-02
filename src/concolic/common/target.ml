
module Make (K : Smt.Symbol.KEY) = struct
  module FSet = Smt.Formula.Set.Make (K)
  type t = { formula_set : FSet.t }
end
