
type t =
  { target_formula : bool Formula.t
  ; all_formulas : Formula.BSet.t
  ; i_env : Input_env.t
  ; id : Utils.Uid.t
  ; priority : Path_priority.t }

let empty : t = 
  { target_formula = Formula.trivial
  ; all_formulas = Formula.BSet.empty
  ; i_env = Input_env.empty
  ; id = Utils.Uid.make_new ()
  ; priority = Path_priority.zero }

(**
  [make last_formula other_formula i_env ~path_priority] makes a target
    whose respective program path has priority [path_priority]. The target
    can be run if [last_formula] and all formulas in [other_formulas]
    are satisfied. [i_env] is an input environment that satisfies
    [other_formulas] in isolation.

    Thus, if [i_env] is extended with the solution to connected component
    of [last_formula] with respect to [other_formulas], then we have an
    input environment that satisfies the made target.

    The made target gets a brand new unique identifier (with respect to
    any other target made in this way), which is the sole means of equality
    and comparison. Therefore, no two targets that represent the same
    program path should be made, or else they will be unequal.
*)
let make (last_formula : bool Formula.t) (other_formulas : Formula.BSet.t) 
  (i_env : Input_env.t) ~(path_priority : Path_priority.t) : t =
  { target_formula = 
    if Formula.is_const last_formula
    then last_formula
    else Formula.BSet.scc last_formula ~wrt:other_formulas
  ; all_formulas = Formula.BSet.add last_formula other_formulas
  ; i_env 
  ; id = Utils.Uid.make_new ()
  ; priority = path_priority }

let compare a b = 
  Utils.Uid.compare a.id b.id

let equal a b = 
  Utils.Uid.equal a.id b.id

let priority ({ priority ; _ } : t) : Path_priority.t =
  priority
