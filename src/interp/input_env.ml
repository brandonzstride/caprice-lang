
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)

  module Key = struct
    type _ t =
      | KBool : K.t -> bool t
      | KInt : K.t -> int t
      | KTag : K.t -> Tag.t t

    let make_bool k = KBool k
    let make_int k = KInt k
    let make_tag k = KTag k
  end

  type t = Input.t Utils.Uid.Map.t

  let empty : t = Utils.Uid.Map.empty

  (* propagates failing extraction *)
  let find_and_extract_exn (extract_exn : Input.t -> 'a) (k : K.t) (m : t) : 'a option =
    Option.map extract_exn (Utils.Uid.Map.find_opt (K.uid k) m)

  let find (type a) (key : a Key.t) (m : t) : a option =
    match key with
    | KBool k -> find_and_extract_exn Input.bool_exn k m
    | KInt k -> find_and_extract_exn Input.int_exn k m
    | KTag k -> find_and_extract_exn Input.tag_exn k m

  let add (type a) (key : a Key.t) (input : a) (m : t) : t =
    let add k i = Utils.Uid.Map.add (K.uid k) i m in
    match key with
    | KBool k -> add k (Input.IBool input)
    | KInt k -> add k (Input.IInt input)
    | KTag k -> add k (Input.ITag input)

  let extend (base_map : t) (extending_map : t) : t =
    Utils.Uid.Map.union (fun _ _ v -> Some v)
      base_map extending_map

  let to_string (m : t) : string =
    "{ " ^ 
      ( Utils.Uid.Map.to_list m
      |> List.map (fun (uid, input) ->
        string_of_int (Utils.Uid.to_int uid) ^ " |-> " ^ Input.to_string input
        )
      |> String.concat " ; ")
    ^ "}"


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
