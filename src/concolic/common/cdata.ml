
(* concolic data *)
type 'a t = 'a * ('a, Stepkey.t) Smt.Formula.t

let equal eq (a, s_a) (b, s_b) = 
  eq a b
  && Smt.Formula.equal s_a s_b

let compare cmp (a, s_a) (b, s_b) =
  match cmp a b with
  | 0 -> Smt.Formula.compare s_a s_b
  | c -> c
