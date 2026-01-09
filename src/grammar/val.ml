
open Lang

include Value.Make (Cdata)

(* 
  True if the value has any non-constant symbolic formula in it.

  This is used to see if recursive functions are called with symbolic
  values when type splaying.
*)
let rec is_symbolic : type a. a t -> bool = fun v ->
  match v with
  | VUnit
  | VGenPoly _
  | VEmptyList
  | VType
  | VTypePoly _
  | VTypeUnit
  | VTypeTop
  | VTypeBottom
  | VTypeInt
  | VTypeBool -> false
  | VInt (_, s) -> not (Smt.Formula.is_const s)
  | VBool (_, s) -> not (Smt.Formula.is_const s)
  (* Recursive cases: is symbolic if any subvalue is *)
  | VVariant { payload = Any v' ; label = _ } -> is_symbolic v'
  | VModule map_body
  | VRecord map_body ->
    Labels.Record.Map.exists (fun _ (Any v') -> is_symbolic v') map_body
  | VTuple (Any v1, Any v2) ->
    is_symbolic v1 || is_symbolic v2
  | VListCons (Any v_hd, v_tl) ->
    is_symbolic v_hd || is_symbolic v_tl
  | VTypeList t ->
    is_symbolic t
  | VTypeRecord record_body ->
    Labels.Record.Map.exists (fun _ t -> is_symbolic t) record_body
  | VTypeVariant variant_body ->
    Labels.Variant.Map.exists (fun _ t -> is_symbolic t) variant_body
  | VTypeTuple (t1, t2) ->
    is_symbolic t1 || is_symbolic t2
  | VTypeSingle t ->
    is_symbolic t
  | VTypeFun { domain ; codomain = CodValue t ; sort = _ }
  | VGenFun { funtype = { domain ; codomain = CodValue t ; sort = _ } ; nonce = _ ; mut_alist = _ } ->
    is_symbolic domain || is_symbolic t
  | VWrapped { data ; tau = { domain ; codomain = CodValue t ; sort = _ } } ->
    is_symbolic data || is_symbolic domain || is_symbolic t
  (* Closures cases: assume true, but may want to inspect closure *)
  | VFunClosure _
  | VFunFix _
  | VTypeModule _
  | VLazy _
  | VTypeMu _
  | VTypeRefine _
  | VGenFun { funtype = { domain = _ ; codomain = CodDependent _ ; sort = _ } ; nonce = _ ; mut_alist = _ }
  | VTypeFun { domain = _ ; codomain = CodDependent _ ; sort = _ }
  | VWrapped { data = _ ; tau = { domain = _ ; codomain = CodDependent _ ; sort = _ } } -> true

let is_any_symbolic (Any v) = is_symbolic v

(**
  [does_wrap_matter t] is true if wrapping some value [v] (which
    has type [t] already) with the type [t] could possibly change
    the usage behavior of the wrapped value.

  For example, [does_wrap_matter VTypeInt] is [false] because the
    int wrapper is a no-op.
  Another example: [does_wrap_matter (VTypeRecord _)] is [true] because
    the record wrapper can hide labels in the value.

  This function is used to avoid adding lazy wrappers to lazily-generated
  values.
*)
let rec does_wrap_matter : typeval t -> bool = function
  | VType
  | VTypePoly _
  | VTypeUnit
  | VTypeTop
  | VTypeBottom
  | VTypeInt
  | VTypeBool
  | VTypeSingle _ -> false
  (* propagate *)
  | VTypeVariant variant_t ->
    Labels.Variant.Map.exists (fun _ -> does_wrap_matter) variant_t
  | VTypeList t
  | VTypeRefine { tau = t ; _ } -> does_wrap_matter t
  | VTypeTuple (t1, t2) -> does_wrap_matter t1 || does_wrap_matter t2
  (* closures (mu), functions, and records/modules need wrap *)
  | VTypeMu _ (* we overapproximate and assume the recursive type wrap can matter *)
  | VTypeFun _ (* function wrapper adds usage checks *)
  | VTypeRecord _ (* record and module wrappers can hide labels *)
  | VTypeModule _ -> true

module X = struct
  type 'a t =
    | Value of ('a * bool Formula.t)
    | SortMismatch

  let of_cdata d = Value d
  let make b = Value (b, Smt.Formula.const_bool b)

  let ( let- ) x f =
    match x with
    | Value (_, Smt.Formula.Const_bool false) -> x
    | Value (a, s) ->
      begin match f () with
      | Value (b, s') -> Value (a && b, Smt.Formula.and_ [ s' ; s ])
      | SortMismatch -> SortMismatch
      end
    | SortMismatch -> SortMismatch

  let rec fold_lists (f : 'a -> 'a -> bool t) (x : 'a list) (y : 'a list) : bool t =
    match x, y with
    | [], [] -> make true
    | [], _ | _, [] -> make false
    | hdx :: xs, hdy :: ys ->
      let- () = f hdx hdy in
      fold_lists f xs ys
end

(**
  [intensional_equal x y] is [Some (b, s)] if [x] and [y] are of the same
    sort, and their components are of the same sort, where [b] is
    the concrete value of their intensional equality, and [s] is the symbolic
    value.
      e.g. [intensional_equal (0, 1) (1, 0)] is [Some (false, s)] for [s] the
        formula describe equality of all symbolic components, which were not
        written at all in the example concrete tuples.

    It is [None] if they are not of the same sort, which indicates a runtime
    type mismatch.
      e.g. [intensional_equal () int] is a mismatch.
      e.g. [intensional_equal (0, 1) true] is a mismatch.

  TODO: if the formula is constant false, then can escape early.
    But that would possibly skip later mismatches. So as long as
    it's clear that the semantics are that something like 
      (b, ()) === (not b, 0)
    for physically equal boolean b is false instead of mismatch,
    then it is a good idea to skip checking () === 0 when we see
    that b is never equal to not b.
*)
let rec intensional_equal (x : any) (y : any) : bool X.t =
  let open X in
  if x == y then make true else
  match x, y with
  (* trivially equal *)
  | Any VUnit, Any VUnit
  | Any VEmptyList, Any VEmptyList
  | Any VType, Any VType
  | Any VTypeUnit, Any VTypeUnit
  | Any VTypeTop, Any VTypeTop
  | Any VTypeBottom, Any VTypeBottom
  | Any VTypeInt, Any VTypeInt
  | Any VTypeBool, Any VTypeBool ->
    make true
  | Any VTypePoly { id = id1 }, Any VTypePoly { id = id2 } ->
    make (id1 = id2)
  (* symbolic equality *)
  | Any VInt (i1, s1), Any VInt (i2, s2) ->
    of_cdata (i1 = i2, Formula.binop Smt.Binop.Equal s1 s2)
  | Any VBool (b1, s1), Any VBool (b2, s2) ->
    of_cdata (b1 = b2, Formula.binop Smt.Binop.Equal s1 s2)
  (* propagate equality *)
  | Any VVariant v1, Any VVariant v2 ->
    if Labels.Variant.equal v1.label v2.label then
      intensional_equal v1.payload v2.payload
    else
      make false
  | Any VListCons (a1, tl1), Any VListCons (a2, tl2) ->
    let- () = intensional_equal a1 a2 in
    iequal tl1 tl2
  | Any VGenPoly g1, Any VGenPoly g2 ->
    if g1.id = g2.id then
      make (g1.nonce = g2.nonce) 
    else
      SortMismatch (* these are of different types *)
  | Any VTuple (l1, r1), Any VTuple (l2, r2) ->
    let- () = intensional_equal l1 l2 in
    intensional_equal r1 r2
  | Any VGenFun { nonce = n1 ; funtype = _ ; mut_alist = _ }
  , Any VGenFun { nonce = n2 ; funtype = _ ; mut_alist = _ } ->
    make (n1 = n2)
  | Any VTypeSingle t1, Any VTypeSingle t2
  | Any VTypeList t1, Any VTypeList t2 ->
    iequal t1 t2
  | Any VTypeTuple (tl1, tr1), Any VTypeTuple (tl2, tr2) ->
    let- () = iequal tl1 tl2 in
    iequal tr1 tr2
  | Any VTypeFun tf1, Any VTypeFun tf2 ->
    iequal_ftype tf1 tf2
  | Any VRecord m1, Any VRecord m2
  | Any VModule m1, Any VModule m2 ->
    fold_lists (fun (l1, v1) (l2, v2) ->
      if Labels.Record.equal l1 l2 then 
        intensional_equal v1 v2
      else
        make false
    ) (Labels.Record.Map.to_list m1) (Labels.Record.Map.to_list m2)
  | Any VTypeRecord m1, Any VTypeRecord m2 ->
    fold_lists (fun (l1, v1) (l2, v2) ->
      if Labels.Record.equal l1 l2 then 
        iequal v1 v2
      else
        make false
    ) (Labels.Record.Map.to_list m1) (Labels.Record.Map.to_list m2)
  | Any VTypeVariant m1, Any VTypeVariant m2 ->
    fold_lists (fun (l1, v1) (l2, v2) ->
      if Labels.Variant.equal l1 l2 then 
        iequal v1 v2
      else
        make false
    ) (Labels.Variant.Map.to_list m1) (Labels.Variant.Map.to_list m2)
  | Any VTypeModule c1, Any VTypeModule c2 ->
    let rec fold bindings (x : Labels.Record.t Ast.typed_item list) (y : Labels.Record.t Ast.typed_item list) =
      match x, y with
      | [], [] -> make true
      | [], _ | _, [] -> make false
      | i1 :: xs, i2 :: ys ->
        if Labels.Record.equal i1.item i2.item then
          let- () =
            equal_closure bindings
              { captured = i1.tau ; env = c1.env }
              { captured = i2.tau ; env = c2.env }
          in
          fold [ Labels.Record.to_ident i1.item, Labels.Record.to_ident i2.item ] xs ys
        else
          make false
    in
    fold [] c1.captured c2.captured
  | Any VTypeRefine r1, Any VTypeRefine r2 ->
    let- () = iequal r1.tau r2.tau in
    equal_closure [ r1.var, r2.var ] r1.predicate r2.predicate
  | Any VFunClosure c1, Any VFunClosure c2 ->
    equal_closure [ c1.param, c2.param ] c1.closure c2.closure
  | Any VFunFix c1, Any VFunFix c2 ->
    equal_closure [ c1.fvar, c2.fvar ; c1.param, c2.param ] c1.closure c2.closure
  | Any VTypeMu c1, Any VTypeMu c2 ->
    equal_closure [ c1.var, c2.var ] c1.closure c2.closure
  | Any VWrapped w1, Any VWrapped w2 ->
    let- () = intensional_equal (Any w1.data) (Any w2.data) in
    iequal_ftype w1.tau w2.tau
  | Any VLazy s1, Any VLazy s2 ->
    if s1.symbol.id = s2.symbol.id then
      fold_lists iequal s1.wrapping_types s2.wrapping_types
    else
      (* for now, say type mismatch if comparing lazy values *)
      SortMismatch
      (* TODO: eventually we want to handle these by asking for lazy environment *)
  | _, _ ->
    (*
      All data has been handled, and anything that is not
      handled above is a sort mismatch.
      Otherwise, the values are not equal, but they are all
      types, so they are of the same sort (type) and are simply
      a constant false, but not error.
    *)
    handle_any x
      ~data:(fun _ -> SortMismatch)
      ~typeval:(fun _ ->
        handle_any y
          ~data:(fun _ -> SortMismatch)
          ~typeval:(fun _ -> make false)
        )

and iequal : type a. a t -> a t -> bool X.t = fun x y ->
  intensional_equal (Any x) (Any y)

and iequal_ftype (tf1 : (typeval t, fun_cod) Funtype.t) (tf2 : (typeval t, fun_cod) Funtype.t) : bool X.t =
  let open X in
  if Funtype.equal_sort tf1.sort tf2.sort then
    let- () = iequal tf1.domain tf2.domain in
    iequal_cod tf1.codomain tf2.codomain
  else
    (* similar to dependent vs nondependent, a deterministic function type 
      is not equal to a nondeterministic function type, but it is not a sort
      mismatch (and this is an overloading of the word "sort") *)
    make false

and iequal_cod cod1 cod2 =
  if cod1 == cod2 then X.make true else
  match cod1, cod2 with
  | CodValue t1, CodValue t2 ->
    intensional_equal (Any t1) (Any t2)
  | CodDependent (id1, c1), CodDependent (id2, c2) ->
    equal_closure [ id1, id2 ] c1 c2
  | _ ->
    (* Both are types, so not failure, but never equal because
      a dependent function is not a non-dependent function. *)
    X.make false

and equal_closure _bindings closure1 closure2 =
  if closure1 == closure2 then
    X.make true
  else 
    SortMismatch

(* This is slower than it could be, but I'm saving code *)
let equal_any x y =
  match intensional_equal x y with
  | Value (b, _) -> b
  | SortMismatch -> false

let equal (type a) (x : a t) (y : a t) : bool =
  equal_any (Any x) (Any y)

let equal_fun_cod cod1 cod2 =
  match iequal_cod cod1 cod2 with
  | Value (b, _) -> b
  | SortMismatch -> false
