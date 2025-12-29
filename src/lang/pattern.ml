
type t =
  | PAny
  | PVariable of Ident.t
  | PVariant of t Variant.t (* payload is a pattern *)
  | PTuple of t * t
  | PEmptyList
  | PDestructList of t * t
  | PPatternOr of t list
  | PPatternAs of t * Ident.t
  [@@deriving eq, ord]

let rec to_string (p : t) : string =
  match p with
  | PAny -> "_"
  | PVariable id -> Ident.to_string id
  | PVariant { label ; payload } ->
    Format.sprintf "%s %s" (Labels.Variant.to_string label) (to_string payload)
  | PTuple (p1, p2) ->
    Format.sprintf "(%s, %s)" (to_string p1) (to_string p2)
  | PEmptyList ->
    "[]"
  | PDestructList (p_hd, p_tl) ->
    Format.sprintf "%s :: %s" (to_string p_hd) (to_string p_tl)
  | PPatternOr p_ls ->
    Format.sprintf "(%s)" (String.concat " | " @@ List.map to_string p_ls)
  | PPatternAs (pat, id) ->
    Format.sprintf "(%s as %s)" (to_string pat) (Ident.to_string id)
