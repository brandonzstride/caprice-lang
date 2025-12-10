
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)

  module Key = struct
    type _ t =
      | KBool : K.t -> bool t
      | KInt : K.t -> int t
      | KLabel : K.t -> Label.t t

    let make_bool k = KBool k
    let make_int k = KInt k
    let make_label k = KLabel k
  end

  type t = Input.t Utils.Uid.Map.t

  let empty : t = Utils.Uid.Map.empty

  let find_and_bind (f : Input.t -> 'a option) (k : K.t) (m : t) : 'a option =
    Option.bind (Utils.Uid.Map.find_opt (K.uid k) m) f

  let find (type a) (key : a Key.t) (m : t) : a option =
    match key with
    | KBool k -> find_and_bind Input.bool_opt k m
    | KInt k -> find_and_bind Input.int_opt k m
    | KLabel k -> find_and_bind Input.label_opt k m

  let add (type a) (key : a Key.t) (input : a) (m : t) : t =
    let add k i = Utils.Uid.Map.add (K.uid k) i m in
    match key with
    | KBool k -> add k (Input.IBool input)
    | KInt k -> add k (Input.IInt input)
    | KLabel k -> add k (Input.ILabel input)

  let extend (base_map : t) (extending_map : t) : t =
    Utils.Uid.Map.union (fun _ _ v -> Some v)
      base_map extending_map

  (**
    [remove_greater max_key t] is the map [t] filtered to only have keys not
    exceeding [max_key].
  *)
  let remove_greater (max_key : K.t) (m : t) : t =
    let new_m, i_opt, _ = Utils.Uid.Map.split (K.uid max_key) m in
    match i_opt with
    | Some i -> Utils.Uid.Map.add (K.uid max_key) i new_m
    | None -> new_m

  let of_model (model : K.t Smt.Model.t) : t =
    List.fold_left (fun acc uid ->
      let v =
        match model.value (I uid) with
        | Some i -> Input.IInt i
        | None -> IBool (Option.get (model.value (B uid)))
      in
      Utils.Uid.Map.add uid v acc
    ) empty model.domain  
end
