
type t =
  { target_formula : bool Formula.t
  ; all_formulas : Formula.BSet.t
  ; i_env : Ienv.t
  ; size : int
  ; id : Utils.Uid.t }

let empty : t = 
  { target_formula = Formula.const_bool true
  ; all_formulas = Formula.BSet.empty
  ; i_env = Ienv.empty
  ; size = 0
  ; id = Utils.Uid.make_new () }

let make (last_formula : bool Formula.t) (all_formulas : Formula.BSet.t) 
  (i_env : Ienv.t) ~(size : int) : t =
  { target_formula = Formula.and_ (last_formula :: Formula.BSet.to_list all_formulas) (* TODO: compute SCC *)
  ; all_formulas 
  ; i_env 
  ; size 
  ; id = Utils.Uid.make_new () }

let compare a b = 
  Utils.Uid.compare a.id b.id

let equal a b = 
  Utils.Uid.equal a.id b.id

let path_length ({ size ; _ } : t) : int =
  size
