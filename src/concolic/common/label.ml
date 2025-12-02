
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
end

include T

(* Labels with alternatives *)
module With_alt = struct
  type t = { main : T.t ; alts : T.t list }
    [@@deriving eq, ord]

  let left = { main = T.left ; alts = [ T.right ] }
  let right = { main = T.right ; alts = [ T.left ] }

  let check = { main = T.check ; alts = [ T.eval ] }
  let eval = { main = T.eval ; alts = [ T.check ] }
end
