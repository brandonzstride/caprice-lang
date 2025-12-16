
(* Comparable type *)
module type S = sig
  type t [@@deriving eq, ord]
end

(* Comparable type with one parameter *)
module type S1 = sig
  type 'a t [@@deriving eq, ord]
end

(* Comparable, printable type with one parameter *)
module type P1 = sig
  include S1
  val to_string : ('a -> string) -> 'a t -> string
end
