
module Make_H (K : Baby.OrderedType) = struct
  module B = Baby.H.Make (K)

  (* TODO: make this faster by actually walking the tree. However
    that would require I modify the source code of Baby. *)
  let random_from_seq ~size seq =
    let n = ref size in
    Seq.find (fun _ ->
      let i = Random.int !n in
      n := !n - 1;
      i = 0
    ) seq

  module Map = struct
    include B.Map
    let domain = B.domain

    let random_binding_opt (m : 'a t) : (K.t * 'a) option =
      random_from_seq ~size:(cardinal m) (to_seq m)
  end

  module Set = struct
    include B.Set

    let random_elt_opt (s : t) : elt option =
      random_from_seq ~size:(cardinal s) (to_seq s)
  end
end
