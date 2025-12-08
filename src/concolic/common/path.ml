
(* Path units *)
type punit =
  | Formula of (bool, Stepkey.t) Smt.Formula.t
  | Label of Stepkey.t Interp.Keyed_label.With_alt.t

type t = punit list

let empty : t = []

let cons_label (l : Stepkey.t Interp.Keyed_label.With_alt.t) (t : t) : t =
  Label l :: t

let cons_formula (e : (bool, Stepkey.t) Smt.Formula.t) (t : t) : t =
  Formula e :: t
