
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)

  module Key = struct
    type _ t =
      | KBool : K.t -> bool t
      | KInt : K.t -> int t
      | KLabel : K.t -> Label.t t
  end

  module KMap  = Baby.H.Map.Make (K)

  type t = Input.t KMap.t

  let empty : t = KMap.empty

  let find_and_bind (f : Input.t -> 'a option) (k : K.t) (m : t) : 'a option =
    Option.bind (KMap.find_opt k m) f

  let find (type a) (key : a Key.t) (m : t) : a option =
    match key with
    | KBool k -> find_and_bind Input.bool_opt k m
    | KInt k -> find_and_bind Input.int_opt k m
    | KLabel k -> find_and_bind Input.label_opt k m

  let add (type a) (key : a Key.t) (input : a) (m : t) : t =
    match key with
    | KBool k -> KMap.add k (Input.IBool input) m
    | KInt k -> KMap.add k (Input.IInt input) m
    | KLabel k -> KMap.add k (Input.ILabel input) m

  (**
    [remove_greater max_key t] is the map [t] filtered to only have keys not
    exceeding [max_key].
  *)
  let remove_greater (max_key : K.t) (m : t) : t =
    let new_m, i_opt, _ = KMap.split max_key m in
    match i_opt with
    | Some i -> KMap.add max_key i new_m
    | None -> new_m
end
