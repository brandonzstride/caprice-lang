
type t =
  { target_formula : bool Formula.t
  ; all_formulas : Formula.BSet.t
  ; i_env : Ienv.t
  ; size : int
  ; id : Utils.Uid.t }

let empty : t = 
  { target_formula = Formula.trivial
  ; all_formulas = Formula.BSet.empty
  ; i_env = Ienv.empty
  ; size = 0
  ; id = Utils.Uid.make_new () }

let make (last_formula : bool Formula.t) (other_formulas : Formula.BSet.t) 
  (i_env : Ienv.t) ~(size : int) : t =
  { target_formula = 
    if Formula.is_const last_formula
    then last_formula
    else Formula.BSet.scc last_formula ~wrt:other_formulas
  ; all_formulas = Formula.BSet.add last_formula other_formulas
  ; i_env 
  ; size 
  ; id = Utils.Uid.make_new () }

let compare a b = 
  Utils.Uid.compare a.id b.id

let equal a b = 
  Utils.Uid.equal a.id b.id

let path_length ({ size ; _ } : t) : int =
  size
