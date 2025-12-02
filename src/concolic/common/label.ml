
module T = struct
  type t = Label of Lang.Ident.t [@@unboxed]
    [@@deriving eq, ord]

  let check = Label (Ident "Check")
  let eval = Label (Ident "Eval")

  let left = Label (Ident "Left")
  let right = Label (Ident "Right")
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
