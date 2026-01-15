
module Make (K : Smt.Symbol.KEY) = struct
  module K = Smt.Symbol.Make_comparable_key (K)

  type t = Input.t Utils.Uid.Map.t

  let empty : t = Utils.Uid.Map.empty

  (* Propagates failing extraction. Is None if the key doesn't exist at all *)
  let find (type a) (kind : a Input.Kind.t) (key : K.t) (m : t) : a option =
    Option.map (Input.extract_exn kind) (Utils.Uid.Map.find_opt (K.uid key) m)

  let add (type a) (kind : a Input.Kind.t) (key : K.t) (input : a) (m : t) : t =
    Utils.Uid.Map.add (K.uid key) (
      match kind with
      | Input.Kind.KBool -> Input.IBool input
      | KInt -> IInt input
      | KTag -> ITag input
    ) m

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

include Make (Stepkey)
