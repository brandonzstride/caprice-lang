
module Make_H (K : Baby.OrderedType) = struct
  module B = Baby.H.Make (K)

  module Map = struct
    include B.Map
    let domain = B.domain

    (* TODO: make this faster by actually walking the tree. However
      that would require I modify the source code. *)
    let random_binding_opt (m : 'a t) : (K.t * 'a) option =
      let n = ref (cardinal m) in
      to_seq m
      |> Seq.find (fun _ ->
        let i = Random.int !n in
        n := !n - 1;
        i = 0
      )
  end

  module Set = struct
    include B.Set

    let random_opt (s : t) : elt option =
      let n = ref (cardinal s) in
      to_seq s
      |> Seq.find (fun _ ->
        let i = Random.int !n in
        n := !n - 1;
        i = 0
      )
  end
end
