
type t = Path_item.t list

let empty : t = []

let cons (pitem : Path_item.t) (t : t) : t =
  pitem :: t

let formulas (t : t) : Formula.BSet.t =
  List.fold_left (fun set -> function
    | Path_item.Formula (formula, _)
    | Nonflipping formula -> Formula.BSet.add formula set
    | Tag _ -> set
  ) Formula.BSet.empty t
