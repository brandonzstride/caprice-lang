
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

let formulas (t : t) : Formula.BSet.t =
  List.fold_left (fun set -> function
    | Formula (formula, _)
    | Nonflipping formula -> Formula.BSet.add formula set
    | Label _ -> set
  ) Formula.BSet.empty t

let priority_of_punit (u : punit) : int =
  match u with
  | Formula _ -> 1
  | Nonflipping _ -> 0
  | Label { label = { main ; _ } ; _ } -> Interp.Label.priority main

let priority (p : t) : int =
  List.fold_left (fun acc u -> acc + priority_of_punit u) 0 p
