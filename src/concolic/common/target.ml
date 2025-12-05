
module Make (K : Smt.Symbol.KEY) = struct
  module FSet = Smt.Formula.Set.Make (K)
  
  let id_counter = Utils.Counter.create ()

  type t =
    { formulas : FSet.t
    ; labels : K.t Timed_label.t list
    ; size : int
    ; id : int }

  let initial_id = Utils.Counter.next id_counter

  let empty : t = 
    { formulas = FSet.empty
    ; labels = []
    ; size = 0
    ; id = initial_id }

  let compare a b = 
    Int.compare a.id b.id

  let equal a b = 
    Int.equal a.id b.id
end
