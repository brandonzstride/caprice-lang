
module Make (K : Smt.Symbol.KEY) = struct
  module FSet = Smt.Formula.Set.Make (K)
  type t =
    { formulas : FSet.t
    ; labels : K.t Timed_label.t list }
end
