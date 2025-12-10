
let id_counter = Utils.Counter.create ()
let next_id () = Utils.Counter.next id_counter

type t =
  { target_formula : bool Formula.t
  ; all_formulas : Formula.BSet.t
  ; i_env : Ienv.t
  ; size : int
  ; id : int }

let initial_id = next_id ()

let empty : t = 
  { target_formula = Formula.const_bool true
  ; all_formulas = Formula.BSet.empty
  ; i_env = Ienv.empty
  ; size = 0
  ; id = initial_id }

let make (last_formula : bool Formula.t) (all_formulas : Formula.BSet.t) 
  (i_env : Ienv.t) ~(size : int) : t =
  { target_formula = Formula.and_ (last_formula :: Formula.BSet.to_list all_formulas) (* TODO: compute SCC *)
  ; all_formulas 
  ; i_env 
  ; size 
  ; id = next_id () }

let compare a b = 
  Int.compare a.id b.id

let equal a b = 
  Int.equal a.id b.id

let path_length ({ size ; _ } : t) : int =
  size
