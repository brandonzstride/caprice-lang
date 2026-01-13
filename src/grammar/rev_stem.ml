(*
  A stem off of a path, represented as a path in reverse order,
  and a total length.

  The stem is constructed from nothing and only begins to cons
  path items if the total length exceeds a set amount.
  of creation.
*)

type t =
  { rev_stem  : Path.t
  ; total_len : Path_length.t }

let empty : t =
  { rev_stem  = Path.empty
  ; total_len = Path_length.zero }

let of_len (total_len : Path_length.t) : t =
  { empty with total_len }

let cons (p_item : Path_item.t) ~(if_exceeds : Path_length.t) (t : t) : t =
  { total_len = Path_length.plus_int t.total_len (Path_item.to_priority p_item)
  ; rev_stem =
    if Path_length.geq t.total_len if_exceeds then
      Path.cons p_item t.rev_stem
    else
      t.rev_stem
  }

let to_forward_path ({ rev_stem ; _ } : t) : Path.t =
  List.rev rev_stem
