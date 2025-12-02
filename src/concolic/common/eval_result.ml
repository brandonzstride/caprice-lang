
module Make (K : Smt.Symbol.KEY) = struct
  module V = Cvalue.Make (K)

  type t =
    | Val of V.any * K.t
    | Res of Check_result.t
end
