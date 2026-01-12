
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
  | VGenFun { funtype = { domain ; codomain = CodValue t ; sort = _ } ; nonce = _ ; alist = _ } ->
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
  | VGenFun { funtype = { domain = _ ; codomain = CodDependent _ ; sort = _ } ; nonce = _ ; alist = _ }
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
  | Any VGenFun { nonce = n1 ; funtype = _ ; alist = _ }
  , Any VGenFun { nonce = n2 ; funtype = _ ; alist = _ } ->
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
            iequal_closure bindings
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
    iequal_closure [ r1.var, r2.var ] r1.predicate r2.predicate
  | Any VFunClosure c1, Any VFunClosure c2 ->
    iequal_closure [ c1.param, c2.param ] c1.closure c2.closure
  | Any VFunFix c1, Any VFunFix c2 ->
    iequal_closure [ c1.fvar, c2.fvar ; c1.param, c2.param ] c1.closure c2.closure
  | Any VTypeMu c1, Any VTypeMu c2 ->
    iequal_closure [ c1.var, c2.var ] c1.closure c2.closure
  | Any VWrapped w1, Any VWrapped w2 ->
    let- () = intensional_equal (Any w1.data) (Any w2.data) in
    iequal_ftype w1.tau w2.tau
  | Any VLazy s1, Any VLazy s2 ->
    if Store.Ref.eq (Obj.magic ()) s1.cell s2.cell then
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
    iequal_closure [ id1, id2 ] c1 c2
  | _ ->
    (* Both are types, so not failure, but never equal because
      a dependent function is not a non-dependent function. *)
    X.make false

(*
  Closure equality will not be a sort mismatch, even if the
  expression references values in the environment of different
  sorts in the same spot. Instead, it is just false.
  
  E.g. This will be false, not a sort mismatch.
    { x |-> 0 } ,
      match x with
      | _ -> true
       end

    { x |-> `None () } ,
       match x with
       | _ -> true
       end
*)
and iequal_closure bindings closure1 closure2 =
  let open X in
  let rec iequal_expr bindings e1 e2 =
    if e1 == e2 && closure1.env == closure2.env then
      (* skip physically equal expressions as long as they are in the same environment *)
      make true
    else
    let ieq = iequal_expr bindings in
    match e1, e2 with
    (* trivially equal *)
    | Ast.EUnit, Ast.EUnit
    | EEmptyList, EEmptyList
    | EPick_i, EPick_i
    | EAbstractType, EAbstractType
    | EType, EType
    | ETypeInt, ETypeInt
    | ETypeBool, ETypeBool
    | ETypeTop, ETypeTop
    | ETypeBottom, ETypeBottom
    | ETypeUnit, ETypeUnit ->
      make true
    | EInt i1, EInt i2 ->
      make (Int.equal i1 i2)
    | EBool b1, EBool b2 ->
      make (Bool.equal b1 b2)
    (* equal values *)
    | EVar id1, EVar id2 ->
      iequal_id bindings id1 id2
    (* propagate equality *)
    | ENot e1, ENot e2
    | EAssert e1, EAssert e2
    | EAssume e1, EAssume e2
    | ETypeList e1, ETypeList e2
    | ETypeSingle e1, ETypeSingle e2 ->
      ieq e1 e2
    | EBinop r1, EBinop r2 ->
      if Binop.equal r1.binop r2.binop then
        let- () = ieq r1.left r2.left in
        ieq r1.right r2.right
      else
        make false
    | EIf r1, EIf r2 ->
      let- () = ieq r1.if_ r2.if_ in
      let- () = ieq r1.then_ r2.then_ in
      ieq r1.else_ r2.else_
    | EAppl r1, EAppl r2 ->
      let- () = ieq r1.func r2.func in
      ieq r1.arg r2.arg
    | EProject r1, EProject r2 ->
      if Labels.Record.equal r1.label r2.label then
        ieq r1.record r2.record
      else
        make false
    | ERecord m1, ERecord m2
    | ETypeRecord m1, ETypeRecord m2 ->
      fold_lists (fun (l1, e1) (l2, e2) ->
        if Labels.Record.equal l1 l2 then 
          ieq e1 e2
        else
          make false
      ) (Labels.Record.Map.to_list m1) (Labels.Record.Map.to_list m2)
    | ETuple (l1, r1), ETuple (l2, r2)
    | EListCons (l1, r1), EListCons (l2, r2) ->
      let- () = ieq l1 l2 in
      ieq r1 r2
    | EVariant r1, EVariant r2 ->
      if Labels.Variant.equal r1.label r2.label then
        ieq r1.payload r2.payload
      else
        make false
    | ETypeVariant l1, ETypeVariant l2 ->
      fold_lists (fun r1 r2 ->
        if Labels.Variant.equal r1.Variant.label r2.label then 
          ieq r1.payload r2.payload
        else
          make false
      ) l1 l2
    (* check closures *)
    | EFunction r1, EFunction r2 ->
      iequal_expr ((r1.param, r2.param) :: bindings) r1.body r2.body
    | ELet r1, ELet r2 ->
      let- () = ieq r1.defn r2.defn in
      let- () = iequal_var_types bindings r1.var r2.var in
      iequal_expr (
        (Ast.id_of_var r1.var, Ast.id_of_var r2.var) :: bindings
      ) r1.body r2.body
    | ELetRec r1, ELetRec r2 ->
      let- () = iequal_var_types bindings r1.var r2.var in
      let bindings =
        (Ast.id_of_var r1.var, Ast.id_of_var r2.var) :: bindings
      in
      let- () = iequal_expr ((r1.param, r2.param) :: bindings) r1.defn r2.defn in
      iequal_expr bindings r1.body r2.body
    | EModule l1, EModule l2 ->
      begin match l1, l2 with
      | [], [] -> make true
      | [], _ | _, [] -> make false
      | s1 :: tl1, s2 :: tl2 ->
        (* compare first statement and continue with remainder of modules *)
        iequal_statement bindings s1 (Ast.EModule tl1) s2 (Ast.EModule tl2)
      end
    | ETypeModule l1, ETypeModule l2 ->
      begin match l1, l2 with
      | [], [] -> make true
      | [], _ | _, [] -> make false
      | d1 :: tl1, d2 :: tl2 ->
        let- () = ieq d1.tau d2.tau in
        if Labels.Record.equal d1.item d2.item then
          let id1 = Labels.Record.to_ident d1.item in
          let id2 = Labels.Record.to_ident d2.item in
          iequal_expr ((id1, id2) :: bindings) (ETypeModule tl1) (ETypeModule tl2)
        else
          make false
      end
    | ETypeRefine r1, ETypeRefine r2 ->
      let- () = ieq r1.tau r2.tau in
      iequal_expr ((r1.var, r2.var) :: bindings) r1.predicate r2.predicate
    | ETypeMu r1, ETypeMu r2 ->
      iequal_expr ((r1.var, r2.var) :: bindings) r1.body r2.body
    | ETypeFun tf1, ETypeFun tf2 ->
      begin match tf1.domain, tf2.domain with 
      | PReg t1, PReg t2 ->
        let- () = ieq t1.tau t2.tau in
        ieq tf1.codomain tf2.codomain
      | PDep t1, PDep t2 ->
        let- () = ieq t1.tau t2.tau in
        iequal_expr ((t1.item, t2.item) :: bindings) tf1.codomain tf2.codomain
      | _ ->
        make false
      end
    | EMatch _l1, EMatch _l2 ->
      (* TODO: implement equal match *)
      make false
    | _ -> make false

  (*
    Compare statements like let-expressions. A body is required.
    Requires equal names.
  *)
  and iequal_statement bindings s1 k1 s2 k2 =
    let name_of_stmt = function
      | Ast.SLet { var ; _ }
      | Ast.SLetRec { var ; _ } -> Ast.id_of_var var
    in
    let- () = make (Ident.equal (name_of_stmt s1) (name_of_stmt s2)) in
    iequal_expr bindings
      (Ast.statement_to_t s1 k1)
      (Ast.statement_to_t s2 k2)

  and iequal_id bindings id1 id2 =
    let de_bruijn_eq =
      List.find_map (fun (d1, d2) ->
        if Ident.equal id1 d1 then
          (* Found bound in left original expression. Make sure also in right *)
          Some (make (Ident.equal id2 d2))
        else if Ident.equal id2 d2 then
          (* Found bound in right but not in left, so these idents are not equal *)
          Some (make false)
        else
          None 
      ) bindings
    in
    match de_bruijn_eq with
    | Some res -> 
      (* We have an answer by looking in the bindings *)
      res
    | None ->
      (* The variables are supposed to bound in the environment *)
      begin match Env.find id1 closure1.env, Env.find id2 closure2.env with
      | Some v1, Some v2 ->
        (* Found the values. Now compare, and turn sort mismatches into false *)
        intensional_equal v1 v2
        (* begin match intensional_equal v1 v2 with
        | SortMismatch -> make false
        | res ->
          res
        end *)
      | None, None ->
        (* Both are not bound. This is strange, but technically they can be equal *)
        make (Ident.equal id1 id2)
      | _ ->
        (* Exactly one of the variables was not bound, so they cannot be equal *)
        make false
      end
  
  (* check that types on variables are the same *)
  and iequal_var_types bindings var1 var2 =
    match var1, var2 with
    | Ast.VarUntyped _, Ast.VarUntyped _ ->
      make true
    | VarTyped t1, VarTyped t2 ->
      iequal_expr bindings t1.tau t2.tau
    | _ ->
      make false
  in

  iequal_expr bindings closure1.captured closure2.captured

(* This is slower than it could be, but I'm saving code and functor
  complexity by implementing it only in the heavy way, above. *)
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

let equal_closure c1 c2 =
  match iequal_closure [] c1 c2 with
  | Value (b, _) -> b
  | _ -> assert false
