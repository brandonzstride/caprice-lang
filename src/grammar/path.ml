
(* Path units *)
type punit =
  | Formula of bool Formula.t * Stepkey.t
  | Nonflipping of bool Formula.t
  | Tag of Stepkey.t Keyed_tag.With_alt.t

type t = punit list

let empty : t = []

let cons_tag (l : Stepkey.t Keyed_tag.With_alt.t) (t : t) : t =
  Tag l :: t

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
    | Tag _ -> set
  ) Formula.BSet.empty t

(*
  Nonflipping formulas must count for the priority because priority is
  used for path length, and since a formula is flipped according to its
  concrete value, not according to its position in the path tree, the
  path length / priority would vary depending on values. We need path
  length to be the same no matter which direction was taking along a
  branch. This is mainly because the path length of a target should be
  computed from the path, and that path does not know whether the formula
  would be flipped had it taken a different direction.
  We could fix this by noting whether the other direction would be flipped,
  but this current fix (of saying all formulas count to path length) is
  easiest.
*)
let priority_of_punit (u : punit) : int =
  match u with
  | Formula _ | Nonflipping _ -> 1
  | Tag { tag = { main ; _ } ; _ } -> Tag.priority main
