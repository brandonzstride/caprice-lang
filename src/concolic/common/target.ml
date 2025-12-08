
module FSet = Smt.Formula.Set.Make (Stepkey)
module KMap = Baby.H.Map.Make (Stepkey)

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
