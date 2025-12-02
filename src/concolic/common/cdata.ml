
(* concolic data *)
type ('a, 'k) t = 'a * ('a, 'k) Smt.Formula.t

let equal eq (a, s_a) (b, s_b) = 
  eq a b
  && Smt.Formula.equal s_a s_b

module Make (K : Smt.Symbol.KEY) = struct
  type nonrec 'a t = ('a, K.t) t

  let equal = equal
end