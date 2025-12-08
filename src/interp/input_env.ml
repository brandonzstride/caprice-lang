
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)
  module M = Baby.H.Map.Make (K)

  type t = Input.t M.t

  let empty : t = M.empty

  let find : K.t -> t -> Input.t option = M.find_opt

  let find_and_bind (f : Input.t -> 'a option) (k : K.t) (m : t) : 'a option =
    Option.bind (find k m) f

  let find_bool_opt : K.t -> t -> bool option = find_and_bind Input.bool_opt
  let find_int_opt : K.t -> t -> int option = find_and_bind Input.int_opt
  let find_label_opt : K.t -> t -> Label.t option = find_and_bind Input.label_opt

  let add : K.t -> Input.t -> t -> t = M.add

  (**
    [remove_greater max_key t] is the map [t] filtered to only have keys not
    exceeding [max_key].
  *)
  let remove_greater (max_key : K.t) (m : t) : t =
    let new_m, i_opt, _ = M.split max_key m in
    match i_opt with
    | Some i -> M.add max_key i new_m
    | None -> new_m
end
