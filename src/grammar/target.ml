
type t =
  { target_formula : bool Formula.t
  ; all_formulas : Formula.BSet.t
  ; i_env : Input_env.t
  ; id : Utils.Uid.t
  ; path_length : Path_length.t }

let empty : t = 
  { target_formula = Formula.trivial
  ; all_formulas = Formula.BSet.empty
  ; i_env = Input_env.empty
  ; id = Utils.Uid.make_new ()
  ; path_length = Path_length.zero }

let make (last_formula : bool Formula.t) (other_formulas : Formula.BSet.t) 
  (i_env : Input_env.t) ~(path_length : Path_length.t) : t =
  { target_formula = 
    if Formula.is_const last_formula
    then last_formula
    else Formula.BSet.scc last_formula ~wrt:other_formulas
  ; all_formulas = Formula.BSet.add last_formula other_formulas
  ; i_env 
  ; id = Utils.Uid.make_new ()
  ; path_length }

let compare a b = 
  Utils.Uid.compare a.id b.id

let equal a b = 
  Utils.Uid.equal a.id b.id

let path_length ({ path_length ; _ } : t) : Path_length.t =
  path_length
