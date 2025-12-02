
type t =
  | BPlus
  | BMinus
  | BTimes
  | BDivide
  | BModulus
  | BEqual
  | BNeq
  | BLessThan
  | BLeq
  | BGreaterThan
  | BGeq
  | BAnd
  | BOr
[@@deriving eq, ord]

let to_string = function
  | BPlus -> "+"
  | BMinus -> "-"
  | BTimes -> "*"
  | BDivide -> "/"
  | BModulus -> "%"
  | BEqual -> "=="
  | BNeq -> "<>"
  | BLessThan -> "<"
  | BLeq -> "<="
  | BGreaterThan -> ">"
  | BGeq -> ">="
  | BAnd -> "&&"
  | BOr -> "||"
