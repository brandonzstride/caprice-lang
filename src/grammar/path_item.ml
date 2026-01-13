
type t =
  | Formula of bool Formula.t * Stepkey.t
  | Nonflipping of bool Formula.t
  | Tag of Tag.With_alt.t * Stepkey.t

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
let to_priority (u : t) : int =
  match u with
  | Formula _ | Nonflipping _ -> 1
  | Tag ({ main ; _ }, _) -> Tag.priority main
