(*
  A stem off of a path, represented as a path in reverse order,
  and a total length.

  The stem is constructed from nothing and only begins to cons
  path items if the total length exceeds a set amount.
  of creation.
*)

type t =
  { rev_stem  : Path.t
  ; total_priority : Path_priority.t }

let empty : t =
  { rev_stem  = Path.empty
  ; total_priority = Path_priority.zero }

let discard_stem ({ total_priority ; _ } : t) : t =
  { empty with total_priority }

let cons (p_item : Path_item.t) ~(if_exceeds : Path_priority.t) (t : t) : t =
  { total_priority = Path_priority.plus_int t.total_priority (Path_item.to_priority p_item)
  ; rev_stem =
    if Path_priority.geq t.total_priority if_exceeds then
      Path.cons p_item t.rev_stem
    else
      t.rev_stem
  }

let to_forward_path ({ rev_stem ; _ } : t) : Path.t =
  List.rev rev_stem
