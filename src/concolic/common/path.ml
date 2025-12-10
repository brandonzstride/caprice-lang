
(* Path units *)
type punit =
  | Formula of bool Formula.t * Stepkey.t
  | Nonflipping of bool Formula.t
  | Label of Stepkey.t Interp.Keyed_label.With_alt.t

type t = punit list

let empty : t = []

let cons_label (l : Stepkey.t Interp.Keyed_label.With_alt.t) (t : t) : t =
  Label l :: t

let cons_formula (e : bool Formula.t) (k : Stepkey.t) (t : t) : t =
  Formula (e, k) :: t

let cons_nonflipping (e : bool Formula.t) (t : t) : t =
  Nonflipping e :: t

let drop_prefix (n : int) (path : t) : t =
  List.drop n path
