
module type KEY = sig
  type t
  val uid : t -> int
end

module Make_comparable_key (K : KEY) = struct
  include K
  let compare a b = Int.compare (uid a) (uid b)
  let equal a b = Int.equal (uid a) (uid b)
end

module X = Utils.Separate.Comparable.Make (Int)

module T = struct
  type ('a, 'k) t = 'a X.t

  let equal = X.equal

  let make_int (k : 'k) (uid : 'k -> int) : (int, 'k) t =
    I (uid k)

  let make_bool (k : 'k) (uid : 'k -> int) : (bool, 'k) t =
    B (uid k)
end

include T

module Make (Key : KEY) = struct
  type 'a t = ('a, Key.t) T.t

  let make_int (k : Key.t) : int t =
    T.make_int k Key.uid

  let make_bool (k : Key.t) : bool t =
    T.make_bool k Key.uid
end
