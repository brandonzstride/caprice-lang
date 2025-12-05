
module Make_BFS (K : Smt.Symbol.KEY) = struct
  module KT = Target.Make (K)

  module Q = Psq.Make (KT) (Int)

  type k = K.t
  type t = BFS of Q.t [@@unboxed]

  let empty : t = BFS Q.empty

  let push_one (BFS q : t) (target : KT.t) : t =
    BFS (Q.push target target.size q)

  let push_list (x : t) (ls : KT.t list) : t =
    List.fold_left push_one x ls

  let remove (BFS q : t) (target : KT.t) : t =
    BFS (Q.remove target q)

  let pop (BFS q : t) : (KT.t * t) option =
    match Q.pop q with
    | Some ((target, _), t) -> Some (target, BFS t)
    | None -> None
end
