
(* Path units *)
type 'k punit =
  | Formula of (bool, 'k) Smt.Formula.t
  | Label of 'k Timed_label.With_alt.t

type 'k t = 'k punit list
