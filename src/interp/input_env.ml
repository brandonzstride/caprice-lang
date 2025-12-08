
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)
  module M = Baby.H.Map.Make (K)

  type t = Input.t M.t

  let empty : t = M.empty

  let find : K.t -> t -> Input.t option = M.find_opt
end
