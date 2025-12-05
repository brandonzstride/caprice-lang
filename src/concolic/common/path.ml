
(* Path units *)
type 'k punit =
  | Formula of (bool, 'k) Smt.Formula.t
  | Label of 'k Timed_label.With_alt.t

type 'k t = 'k punit list

let empty : 'k t = []

let cons_label (l : 'k Timed_label.With_alt.t) (t : 'k t) : 'k t =
  Label l :: t

let cons_formula (e : (bool, 'k) Smt.Formula.t) (t : 'k t) : 'k t =
  Formula e :: t
