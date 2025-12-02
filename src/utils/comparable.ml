
(* Comparable type *)
module type S = sig
  type t [@@deriving eq, ord]
end

(* Comparable type with one parameter *)
module type S1 = sig
  type 'a t [@@deriving eq, ord]
end
