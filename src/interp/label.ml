
module T = struct
  type t =
    | Check
    | Eval
    | Left
    | Right
    | Label of Lang.Ident.t
    [@@deriving eq, ord]

  let check = Check
  let eval = Eval
  let left = Left
  let right = Right

  let of_variant_label vlabel =
    Label (Lang.Labels.Variant.to_ident vlabel)

  let of_record_label rlabel =
    Label (Lang.Labels.Record.to_ident rlabel)
end

include T

let to_string = function
  | Check -> "Check"
  | Eval -> "Eval"
  | Left -> "Left"
  | Right -> "Right"
  | Label Ident s -> s

(* Labels with alternatives *)
module With_alt = struct
  type t = { main : T.t ; alts : T.t list }
    [@@deriving eq, ord]

  let left = { main = T.left ; alts = [ T.right ] }
  let right = { main = T.right ; alts = [ T.left ] }

  let check = { main = T.check ; alts = [ T.eval ] }
  let eval = { main = T.eval ; alts = [ T.check ] }
end
