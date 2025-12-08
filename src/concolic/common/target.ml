
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)
  module FSet = Smt.Formula.Set.Make (K)
  module KMap = Baby.H.Map.Make (K)
  
  let id_counter = Utils.Counter.create ()

  type t =
    { formulas : FSet.t
    ; labels : Interp.Label.t KMap.t
    ; size : int
    ; id : int }

  let initial_id = Utils.Counter.next id_counter

  let empty : t = 
    { formulas = FSet.empty
    ; labels = KMap.empty
    ; size = 0
    ; id = initial_id }

  let compare a b = 
    Int.compare a.id b.id

  let equal a b = 
    Int.equal a.id b.id
end
