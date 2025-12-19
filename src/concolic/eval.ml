
open Lang
open Common
open Effects
open Cvalue

(* `Any` is unboxed, so this is zero overhead *)
let[@inline always] return_any v = return (Any v)

let bad_input_env : 'a. unit -> 'a = fun () ->
  raise @@ InvariantException "Input environment is ill-formed"

open Cvalue.Error_messages
open Ienv.Key

let eval
  (pgm : Ast.statement list)
  (input_env : Ienv.t)
  (target : Target.t)
  ~(max_step : Interp.Step.t)
  ~(do_splay : bool)
  : Eval_result.t * Logged_run.t list
  =
  (*
    ----------------------------
    EVALUATE EXPRESSION TO VALUE 
    ----------------------------
  *)
  let rec eval (expr : Ast.t) : Cvalue.any m =
    let* () = incr_step ~max_step in
    match expr with
    (* concrete values *)
    | EUnit -> return_any VUnit
    | EInt i -> return_any (VInt (i, Smt.Formula.const_int i))
    | EBool b -> return_any (VBool (b, Smt.Formula.const_bool b))
    | EVar id -> fetch id
    | EFunction { param ; body } ->
      let* env = read in
      return_any (VFunClosure { param ; closure = { captured = body ; env }})
    | ERecord e_record_body -> 
      let* record_body =
        Record.fold (fun l e acc_m ->
          let* acc = acc_m in
          let* v = eval e in
          return (Labels.Record.Map.add l v acc)
        ) (return Record.empty) e_record_body
      in
      return_any (VRecord record_body)
    | EModule stmt_ls ->
      eval_statement_list stmt_ls
    | ETypeModule items ->
      let* env = read in
      return_any (VTypeModule { captured = items ; env })
    | ELet { var ; defn ; body } ->
      let* (binding, v) = eval_statement (SLet { var ; defn }) in
      local (Env.set binding v) (eval body)
    | ELetRec { var ; param ; defn ; body } ->
      let* (binding, v) = eval_statement (SLetRec { var ; param ; defn }) in
      local (Env.set binding v) (eval body)
    | EAppl { func ; arg } ->
      let* v_func = force_eval func in
      begin match v_func with
      | Any VFunClosure { param ; closure = { captured ; env } } ->
        let* v_arg = eval arg in
        local (fun _ -> Env.set param v_arg env) (eval captured)
      | (Any VFunFix { fvar ; param ; closure = { captured ; env } }) as vfun ->
        let* v_arg = eval arg in
        local (fun _ -> 
          Env.set fvar vfun env
          |> Env.set param v_arg
        ) (eval captured)
      | Any VGenFun { domain ; codomain } ->
        let* v_arg = eval arg in
        let* l = read_input make_label input_env in
        let check_f =
          let* () = push_and_log_label Check in
          check v_arg domain
        in
        let eval_f =
          let* () = push_and_log_label Eval in
          match codomain with
          | CodValue cod_tval -> gen cod_tval
          | CodDependent (id, { captured ; env }) ->
            let* cod_tval = local (fun _ -> Env.set id v_arg env) (eval_type captured) in
            gen cod_tval
        in
        begin match l with
        | Some Check -> check_f
        | Some Eval -> eval_f
        | Some _ -> bad_input_env ()
        | None -> let* () = fork check_f in eval_f
        end
      | _ -> mismatch @@ apply_non_function v_func
      end
    | EMatch { subject ; patterns } ->
      (* FIXME: force eval as deep as the pattern needs, not just to WHNF *)
      let* v = force_eval subject in
      let rec find_match = function
        | [] -> mismatch @@ missing_pattern v (List.map fst patterns)
        | (pat, body) :: tl ->
          begin match matches_any pat v with
          | Match -> eval body
          | Match_bindings e -> local (fun env -> Env.extend env e) (eval body)
          | No_match -> find_match tl
          | Failure msg -> fail (Mismatch msg)
          end
      in
      find_match patterns
    | EProject { record ; label } ->
      let* v = force_eval record in
      begin match v with
      | Any VRecord map_body
      | Any VModule map_body ->
        begin match Labels.Record.Map.find_opt label map_body with
        | Some v' -> return v'
        | None -> mismatch @@ missing_label v label
        end
      | _ -> mismatch @@ project_non_record v label
      end
    | EVariant { label ; payload } ->
      let* v = eval payload in
      return_any (VVariant { label ; payload = v })
    | ETuple (e1, e2) ->
      let* v1 = eval e1 in
      let* v2 = eval e2 in
      return_any (VTuple (v1, v2))
    | EEmptyList ->
      return_any VEmptyList
    | EListCons (e1, e2) ->
      let* v1 = eval e1 in
      let* v2 = force_eval e2 in (* FIXME: special case on generated list *)
      begin match v2 with
      | Any (VEmptyList as tl)
      | Any (VListCons _ as tl) -> return_any (VListCons (v1, tl))
      | _ -> mismatch @@ cons_non_list v1 v2
      end
    | EAbstractType ->
      gen VType
    | ETypeSingle e ->
      let* tval = eval_type e in
      return_any (VTypeSingle tval)
    (* symbolic values and branching *)
    | EPick_i ->
      let* step = step in
      let* i = read_and_log_input_with_default make_int input_env ~default:0 in
      return_any (VInt (i, Stepkey.int_symbol step))
    | ENot e ->
      let* v = force_eval e in
      begin match v with
      | Any VBool (b, s) -> return_any (VBool (not b, Smt.Formula.not_ s))
      | _ -> mismatch @@ not_non_bool v
      end
    | EBinop { left ; binop ; right } ->
      eval_binop left binop right
    | EIf { if_ ; then_ ; else_ } ->
      let* v = force_eval if_ in
      begin match v with
      | Any VBool (b, s) ->
        let cont = if b then then_ else else_ in
        let* () = push_formula (if b then s else Smt.Formula.not_ s) in
        eval cont 
      | _ -> mismatch @@ if_non_bool v
      end
    | EAssert e ->
      let* v = force_eval e in
      begin match v with
      | Any VBool (b, s) ->
        if b then
          let* () = push_formula s in
          return_any VUnit
        else
          let* () = push_formula (Smt.Formula.not_ s) in
          fail Assert_false
      | _ -> mismatch @@ assert_non_bool v
      end
    | EAssume e ->
      let* v = force_eval e in
      begin match v with
      | Any VBool (b, s) ->
        if b then
          let* () = push_formula ~allow_flip:false s in
          return_any VUnit
        else
          let* () = push_formula (Smt.Formula.not_ s) in
          fail Vanish
      | _ -> mismatch @@ assume_non_bool v
      end
    (* types *)
    | EType -> return_any VType
    | ETypeInt -> return_any VTypeInt
    | ETypeBool -> return_any VTypeBool
    | ETypeTop -> return_any VTypeTop
    | ETypeBottom -> return_any VTypeBottom
    | ETypeUnit -> return_any VTypeUnit
    | ETypeRecord t_record_body -> 
      let* record_body =
        Record.fold (fun l e acc_m ->
          let* acc = acc_m in
          let* tval = eval_type e in
          return (Labels.Record.Map.add l tval acc)
        ) (return Record.empty) t_record_body
      in
      return_any (VTypeRecord record_body)
    | ETypeFun { domain = PReg { tau } ; codomain } ->
      let* dom_t = eval_type tau in
      let* cod_t = eval_type codomain in
      return_any (VTypeFun { domain = dom_t ; codomain = CodValue cod_t })
    | ETypeFun { domain = PDep { item ; tau } ; codomain } ->
      let* dom_t = eval_type tau in
      let* env = read in
      return_any (VTypeFun { domain = dom_t ; codomain = CodDependent (item, { captured = codomain ; env }) })
    | ETypeRefine { var ; tau ; predicate } ->
      let* tval = eval_type tau in
      let* env = read in
      return_any (VTypeRefine { var ; tau = tval ; predicate = { captured = predicate ; env }})
    | ETypeMu { var ; body } ->
      let* env = read in
      return_any (VTypeMu { var ; closure = { captured = body ; env } })
    | ETypeList e ->
      let* t = eval_type e in
      return_any (VTypeList t)
    | ETypeVariant ls ->
      let* variant_bodies =
        List.fold_left (fun acc_m { Variant.label ; payload } ->
          let* acc = acc_m in
          let* tval = eval_type payload in
          return (Labels.Variant.Map.add label tval acc)
        ) (return Labels.Variant.Map.empty) ls
      in
      return_any (VTypeVariant variant_bodies)

  (*
    ----------------------------------
    EVALUATE BINARY OPERATION TO VALUE
    ----------------------------------
  *)
  and eval_binop (left : Ast.t) (op : Binop.t) (right : Ast.t) : Cvalue.any m =
    let* vleft = force_eval left in
    match op with
    | BAnd -> (* Handle short-circuit && *)
      begin match vleft with
      | Any VBool (true, s) ->
        (* The short-circuiting is effectively a branch, so log the formula *)
        let* () = push_formula s in
        let* vright = force_eval right in
        begin match vright with
        | Any VBool _ -> return vright
        | _ -> mismatch @@ bad_binop vleft op vright
        end
      | Any VBool (false, s) ->
        let* () = push_formula (Smt.Formula.not_ s) in
        return vleft
      | _ -> mismatch @@ bad_binop vleft op (Any VUnit) (* placeholder RHS for And *)
      end
    | BOr -> (* Handle short-circuit || *)
      begin match vleft with
      | Any VBool (true, s) ->
        let* () = push_formula s in
        return vleft
      | Any VBool (false, s) ->
        let* () = push_formula (Smt.Formula.not_ s) in
        let* vright = force_eval right in
        begin match vright with
        | Any VBool _ -> return vright
        | _ -> mismatch @@ bad_binop vleft op vright
        end
      | _ -> mismatch @@ bad_binop vleft op (Any VUnit) (* placeholder RHS for Or *)
      end
    | _ ->
      let* vright = force_eval right in
      let fail_binop = mismatch @@ bad_binop vleft op vright in
      let value_binop a b =
        let k f s1 s2 op =
          return_any @@ f (Smt.Formula.binop op s1 s2)
        in
        let v_int n s = VInt (n, s) in
        let v_bool n s = VBool (n, s) in
        match op, a, b with
        | BPlus        , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_int (n1 + n2)) e1 e2 Plus
        | BMinus       , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_int (n1 - n2)) e1 e2 Minus
        | BTimes       , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_int (n1 * n2)) e1 e2 Times
        | BDivide      , VInt (n1, e1)  , VInt (n2, e2) when n2 <> 0 -> k (v_int (n1 / n2)) e1 e2 Divide
        | BModulus     , VInt (n1, e1)  , VInt (n2, e2) when n2 <> 0 -> k (v_int (n1 mod n2)) e1 e2 Modulus
        | BEqual       , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_bool (n1 = n2)) e1 e2 Equal
        | BEqual       , VBool (b1, e1) , VBool (b2, e2)             -> k (v_bool (b1 = b2)) e1 e2 Equal
        | BNeq         , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_bool (n1 <> n2)) e1 e2 Not_equal
        | BLessThan    , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_bool (n1 < n2)) e1 e2 Less_than
        | BLeq         , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_bool (n1 <= n2)) e1 e2 Less_than_eq
        | BGreaterThan , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_bool (n1 > n2)) e1 e2 Greater_than
        | BGeq         , VInt (n1, e1)  , VInt (n2, e2)              -> k (v_bool (n1 >= n2)) e1 e2 Greater_than_eq
        (* | BOr          , VBool (b1, e1) , VBool (b2, e2)             -> k (v_bool (b1 || b2)) e1 e2 Or
        | BAnd         , VBool (b1, e1) , VBool (b2, e2) -> return_any @@ VBool (b1 && b2, Smt.Formula.and_ [ e1 ; e2 ]) *)
        | _ -> fail_binop
      in
      handle_any vleft
        ~data:(fun data_left ->
          handle_any vright
            ~data:(fun data_right -> value_binop data_left data_right)
            ~typeval:(fun _ -> fail_binop)
        )
        ~typeval:(fun type_left ->
          handle_any vright
            ~data:(fun _ -> fail_binop)
            ~typeval:(fun type_right ->
              match op with
              | BTimes -> return_any (VTypeTuple (type_left, type_right))
              | _ -> fail_binop
            )
        )

  (*
    ---------------------------------
    EVALUATE EXPRESSION TO TYPE VALUE
    ---------------------------------
  *)
  and eval_type (expr : Ast.t) : Cvalue.tval m =
    let* v = force_eval expr in
    handle_any v
      ~data:(fun d -> mismatch @@ non_type_value d)
      ~typeval:return

  (*
    -------------------------
    CHECK FOR TYPE REFUTATION
    -------------------------
  *)
  and check : 'a. Cvalue.any -> Cvalue.tval -> 'a m = fun v t ->
    let refute = fail (Refutation (v, t)) in
    let confirm = fail Confirmation in
    let* () = incr_step ~max_step in
    (* In just about every case except checking mu type, we want to force the value. *)
    (* Even though it is wordy, we do this forcing inside each case. *)
    match t with
    | VTypeInt ->
      let* v = force_value v in
      begin match v with
      | Any VInt _ -> confirm
      | _ -> refute
      end
    | VTypeBool ->
      let* v = force_value v in
      begin match v with
      | Any VBool _ -> confirm
      | _ -> refute
      end
    | VTypeUnit ->
      let* v = force_value v in
      begin match v with
      | Any VUnit -> confirm
      | _ -> refute
      end
    | VTypeTop -> failwith "Unimplemented check top"
    | VTypeBottom -> refute
    | VTypePoly { id } ->
      let* v = force_value v in
      begin match v with
      | Any VGenPoly { id = id' ; nonce = _ } when id = id' -> confirm
      | _ -> refute
      end
    | VType ->
      (* TODO: consider a wellformedness check *)
      let* v = force_value v in
      handle_any v ~data:(fun _ -> refute) ~typeval:(fun _ -> confirm)
    | VTypeFun { domain ; codomain } ->
      let* v = force_value v in
      begin match v with
      | Any VFunClosure { param ; closure = { captured ; env } } ->
        let* genned = gen domain in
        let* res = local (fun _ -> Env.set param genned env) (eval captured) in
        begin match codomain with
        | CodValue cod_tval -> check res cod_tval
        | CodDependent (id, closure) ->
          let* cod_tval = local (fun _ -> Env.set id genned closure.env) (eval_type closure.captured) in
          check res cod_tval
        end
      | (Any VFunFix { fvar ; param ; closure = { captured ; env } }) as vfun ->
        let* genned = gen domain in
        let* res = local (fun _ -> 
            Env.set fvar vfun env
            |> Env.set param genned
          ) (eval captured)
        in
        (* TODO: remove this duplication with the above *)
        begin match codomain with
        | CodValue cod_tval -> check res cod_tval
        | CodDependent (id, { captured ; env }) ->
          let* cod_tval = local (fun _ -> Env.set id genned env) (eval_type captured) in
          check res cod_tval
        end
      | Any VGenFun { domain = domain' ; codomain = codomain' } ->
        let* l_opt = read_input make_label input_env in
        let check_left =
          let* () = push_and_log_label Left in
          if domain = domain' then confirm else
          let* genned = gen domain in
          check genned domain'
        in
        let check_right =
          let* () = push_and_log_label Right in
          if codomain = codomain' then confirm else
          let* cod_tval, cod_tval' =
            match codomain, codomain' with
            | CodValue cod_tval, CodValue cod_tval' -> 
              return (cod_tval, cod_tval')
            | _ ->
              let* genned = gen domain in
              let evaluate cod =
                match cod with
                | CodValue t -> return t
                | CodDependent (id, { captured ; env }) ->
                  local (fun _ -> Env.set id genned env) (eval_type captured)
              in
              let* cod_tval = evaluate codomain in
              let* cod_tval' = evaluate codomain' in
              return (cod_tval, cod_tval')
          in
          if cod_tval = cod_tval' then confirm else
          let* genned' = gen cod_tval' in
          check genned' cod_tval
        in
        begin match l_opt with
        | Some Left -> check_left
        | Some Right -> check_right
        | Some _ -> bad_input_env ()
        | None -> let* () = fork check_left in check_right
        end
      | _ -> refute
      end
    | VTypeVariant variant_t ->
      let* v = force_value v in
      begin match v with
      | Any VVariant { label ; payload } ->
        begin match Labels.Variant.Map.find_opt label variant_t with
        | Some t -> check payload t
        | None -> refute
        end
      | _ -> refute
      end
    | VTypeRecord record_t ->
      let* v = force_value v in
      begin match v with
      | Any VRecord record_v ->
        let t_labels = Record.label_set record_t in
        let v_labels = Record.label_set record_v in
        if Labels.Record.Set.subset t_labels v_labels
        then
          let push_and_check label =
            (* alternatives do not matter when we are running every label right now *)
            let* () = push_and_log_label (Interp.Label.of_record_label label) in
            check
              (Labels.Record.Map.find label record_v)
              (Labels.Record.Map.find label record_t)
          in
          let* l_opt = read_input make_label input_env in
          match l_opt with
          | Some Label id -> push_and_check (Labels.Record.RecordLabel id)
          | Some _ -> bad_input_env ()
          | None ->
            (* is in exploration mode, so we want to check them all *)
            begin match Labels.Record.Set.choose_opt t_labels with
            | Some main_label ->
              let* () =
                let rec go = function
                  | [] -> return ()
                  | label :: tl ->
                    let* () = fork (push_and_check label) in
                    go tl
                in
                Labels.Record.Set.remove main_label t_labels
                |> Labels.Record.Set.to_list
                |> go
              in
              push_and_check main_label
            | None -> confirm
            end
        else refute
      | _ -> refute
      end
    | VTypeMu { var ; closure = { captured ; env } } ->
      begin match v with
      | Any VLazy s ->
        let* lazy_v = find_symbol s in
        begin match lazy_v with
        | LValue v -> check v t
        | LGenList _ -> refute (* TODO: make error message description; it will be cryptic like this *)
        | LGenMu { var = var' ; closure = { captured = captured' ; env = env' } } ->
          (* FIXME: these names (with the "prime") go the other direction as the spec *)
          if captured' = captured && env = env' then confirm else
          let* a = gen VType in (* fresh type to use as a stub *)
          let* t_body = local (fun _ -> Env.set var a env) (eval_type captured) in
          let* t_body' = local (fun _ -> Env.set var' a env') (eval_type captured') in
          if t_body = t_body' then confirm else
          let* genned = gen t_body' in
          check genned t_body
        end
      | _ ->
        let* t_body = local (fun _ -> Env.set var (Any t) env) (eval_type captured) in
        check v t_body
      end
    | VTypeList t ->
      begin match v with
      | Any VLazy s ->
        let* lazy_v = find_symbol s in
        begin match lazy_v with
        | LValue v -> check v (VTypeList t) (* TODO: don't reconstruct *)
        | LGenMu _ -> refute (* see mu todo *)
        | LGenList t' ->
          if t' = t then confirm else
          let* genned = gen t' in
          check genned t
        end
      | Any VEmptyList -> confirm
      | Any VListCons (v_hd, v_tl) ->
        let* l_opt = read_input make_label input_env in
        let check_hd =
          let* () = push_and_log_label Left in
          check v_hd t
        in
        let check_tl =
          let* () = push_and_log_label Right in
          check (Any v_tl) (VTypeList t)
        in
        begin match l_opt with
        | Some Left -> check_hd
        | Some Right -> check_tl
        | Some _ -> bad_input_env ()
        | None -> let* () = fork check_hd in check_tl
        end
      | _ -> refute
      end
    | VTypeRefine { var ; tau ; predicate = { captured ; env } } ->
      (* Value is not directly used here, so we don't force it *)
      let* l_opt = read_input make_label input_env in
      let check_t =
        let* () = push_and_log_label Check in
        check v tau
      in
      let eval_pred =
        let* () = push_and_log_label Eval in
        let* p = local (fun _ -> Env.set var v env) (eval captured) in
        match p with
        | Any VBool (b, s) ->
          if b then 
            let* () = push_formula s in
            confirm
          else 
            let* () = push_formula ~allow_flip:false (Smt.Formula.not_ s) in
            refute
        | _ -> mismatch @@ non_bool_predicate p
      in
      begin match l_opt with
      | Some Check -> check_t
      | Some Eval -> eval_pred
      | Some _ -> bad_input_env ()
      | None -> let* () = fork check_t in eval_pred
      end
    | VTypeTuple (t1, t2) ->
      let* v = force_value v in
      begin match v with
      | Any VTuple (v1, v2) ->
        let* l_opt = read_input make_label input_env in
        let check_left =
          let* () = push_and_log_label Left in
          check v1 t1
        in
        let check_right =
          let* () = push_and_log_label Right in
          check v2 t2
        in
        begin match l_opt with
        | Some Left -> check_left
        | Some Right -> check_right
        | Some _ -> bad_input_env ()
        | None -> let* () = fork check_left in check_right
        end
      | _ -> refute
      end
    | VTypeModule { captured ; env } ->
      let* v = force_value v in
      begin match v with
      | Any VModule module_v ->
        let t_labels_ls = List.map (fun { Ast.item ; _ } -> item) captured in
        let t_labels = Labels.Record.Set.of_list t_labels_ls in
        let v_labels = Record.label_set module_v in
        if Labels.Record.Set.subset t_labels v_labels
        then
          let push_and_check label =
            (* alternatives do not matter when we are running every label right now *)
            let* () = push_and_log_label (Interp.Label.of_record_label label) in
            let new_env, tau = 
              (* TODO: share this computation because it is redone on every fork *)
              Utils.List_utils.fold_left_until (fun env { Ast.item = label' ; tau } ->
                if Labels.Record.equal label' label
                then `Stop (env, tau)
                else `Continue (
                  Env.set (Labels.Record.to_ident label') (Labels.Record.Map.find label' module_v) env
                )
              ) (fun _ -> raise @@ InvariantException "Label not found in module type") env captured
            in
            let* t = local (fun _ -> new_env) (eval_type tau) in
            check (Labels.Record.Map.find label module_v) t
          in
          let* l_opt = read_input make_label input_env in
          match l_opt with
          | Some Label id -> push_and_check (Labels.Record.RecordLabel id)
          | Some _ -> bad_input_env ()
          | None ->
            (* is in exploration mode, so we want to check them all *)
            begin match t_labels_ls with
            | [] -> confirm
            | main_label :: _ ->
              let* () =
                let rec go = function
                  | [] -> return ()
                  | label :: tl ->
                    let* () = fork (push_and_check label) in
                    go tl
                in
                Labels.Record.Set.remove main_label t_labels
                |> Labels.Record.Set.to_list
                |> go
              in
              push_and_check main_label
            end
        else refute
      | _ -> refute
      end
    | VTypeSingle tval ->
      let* v = force_value v in
      handle_any v
        ~data:(fun _ -> refute)
        ~typeval:(fun tval' ->
          if tval' = tval then confirm else
          let* l_opt = read_input make_label input_env in
          let check_subset =
            let* () = push_and_log_label Left in
            let* genned = gen tval' in
            check genned tval
          in
          let check_superset =
            let* () = push_and_log_label Right in
            let* genned = gen tval in
            check genned tval'
          in
          match l_opt with
          | Some Left -> check_subset
          | Some Right -> check_superset
          | Some _ -> bad_input_env ()
          | None -> let* () = fork check_subset in check_superset
        )

  (*
    -------------------------
    GENERATE MEMBER OF A TYPE
    -------------------------
  *)
  and gen (t : Cvalue.tval) : Cvalue.any m =
    let* () = incr_step ~max_step in
    match t with
    | VTypeUnit -> return_any VUnit
    | VTypeInt ->
      let* step = step in
      let* i = read_and_log_input_with_default make_int input_env ~default:0 in
      return_any (VInt (i, Stepkey.int_symbol step))
    | VTypeBool ->
      let* step = step in
      let* b = read_and_log_input_with_default make_bool input_env ~default:false in
      return_any (VBool (b, Stepkey.bool_symbol step))
    | VTypeFun tfun ->
      return_any (VGenFun tfun)
    | VType ->
      let* Step id = step in (* will use step for a fresh integer *)
      return_any (VTypePoly { id })
    | VTypePoly { id } ->
      let* Step nonce = step in (* will use step for a fresh nonce *)
      return_any (VGenPoly { id ; nonce })
    | VTypeTop -> failwith "Unimplemented top gen"
    | VTypeBottom -> fail Vanish
    | VTypeRecord record_t ->
      let* genned_body =
        Record.fold (fun l t acc_m ->
          let* acc = acc_m in
          let* v = gen t in
          return (Labels.Record.Map.add l v acc)
        ) (return Record.empty) record_t
      in
      return_any (VRecord genned_body)
    | VTypeVariant variant_t ->
      let t_labels = Labels.Variant.B.domain variant_t in
      let* l =
        read_and_log_input_with_default make_label input_env
          (* TODO: choose a nonrecursive variant constructor instead of an arbitrary one *)
          ~default:(Interp.Label.of_variant_label (Labels.Variant.Set.choose t_labels))
      in
      begin match l with
      | Label id ->
        let to_gen = Labels.Variant.of_ident id in
        let t = Labels.Variant.Map.find to_gen variant_t in
        let* () =
          push_label Interp.Label.With_alt.{ main = l ; alts =
            Labels.Variant.Set.remove to_gen t_labels
            |> Labels.Variant.Set.to_list
            |> List.map Interp.Label.of_variant_label
          }
        in
        let* payload = gen t in
        return_any (VVariant { label = to_gen ; payload })
      | _ -> bad_input_env ()
      end
    | VTypeList t ->
      if do_splay then (* see the todo on force_eval *)
        let* Step id = step in (* use step as fresh identifier *)
        let* () = add_symbol { id } (LGenList t) in
        return_any (VLazy { id })
      else
        force_gen_list t
    | VTypeRefine { var ; tau ; predicate = { captured ; env } } ->
      let* v = gen tau in
      let* p = local (fun _ -> Env.set var v env) (eval captured) in
      begin match p with
      | Any VBool (true, s) ->
        let* () = push_formula ~allow_flip:false s in
        return v
      | Any VBool (false, s) ->
        let* () = push_formula (Smt.Formula.not_ s) in
        fail Vanish
      | _ -> mismatch @@ non_bool_predicate p
      end 
    | VTypeMu { var ; closure } ->
      if do_splay then (* see the todo on force_eval *)
        let* Step id = step in (* use step as fresh identifier *)
        let* () = add_symbol { id } (LGenMu { var ; closure }) in
        return_any (VLazy { id })
      else
        force_gen_mu var closure
    | VTypeTuple (t1, t2) ->
      let* v1 = gen t1 in
      let* v2 = gen t2 in
      return_any (VTuple (v1, v2))
    | VTypeModule { captured ; env } ->
      let rec fold_labels acc_m = function
        | [] -> acc_m
        | { Ast.item ; tau } :: tl ->
          let* acc = acc_m in
          let* tval = eval_type tau in
          let* v = gen tval in
          local (Env.set (Labels.Record.to_ident item) v) (
            fold_labels (return @@ Labels.Record.Map.add item v acc) tl
          )
      in
      let* genned_body =
        local (fun _ -> env) (
          fold_labels (return Labels.Record.Map.empty) captured
        )
      in
      return_any (VModule genned_body)
    | VTypeSingle tval ->
      return_any tval

  and force_gen_list (body : Cvalue.tval) : Cvalue.any m =
    let* l = read_and_log_input_with_default make_label input_env ~default:Left in
    match l with
    | Left ->
      let* () = push_label Interp.Label.With_alt.left in
      return_any VEmptyList
    | Right ->
      let* () = push_label Interp.Label.With_alt.right in
      let* hd = gen body in
      let* Any tl = gen (VTypeList body) in
      return_any (VListCons (hd, Obj.magic tl)) (* MAGIC: Safe because always returns data *)
    | _ -> bad_input_env ()

  and force_gen_mu (var : Ident.t) (closure : Ast.t Cvalue.closure) : Cvalue.any m =
    let* t_body = 
      local (fun _ -> Env.set var (Any (VTypeMu { var ; closure })) closure.env) 
        (eval_type closure.captured)
    in
    gen t_body


  (*
    ---------------------------------------
    EVALUATE LIST OF STATEMENTS TO A MODULE
    ---------------------------------------
  *)
  and eval_statement_list (statements : Ast.statement list) : Cvalue.any m =
    let rec fold_stmts acc_m = function
      | [] -> acc_m
      | stmt :: tl ->
        let* acc = acc_m in
        let* (id, v) = eval_statement stmt in
        local (Env.set id v) (
          fold_stmts (return @@ Labels.Record.Map.add (Labels.Record.of_ident id) v acc) tl
        )
    in
    let* module_body =
      fold_stmts (return Labels.Record.Map.empty) statements
    in
    return_any (VModule module_body)

  (*
    -------------------------------
    EVALUATE STATEMENT TO A BINDING
    -------------------------------
  *)
  and eval_statement (stmt : Ast.statement) : (Ident.t * Cvalue.any) m =
    match stmt with
    | SLet { var = VarUntyped { name } ; defn } ->
      let* v = eval defn in
      return (name, v)
    | SLetRec { var = VarUntyped { name } ; param ; defn } ->
      let* env = read in
      let v = to_any (VFunFix { fvar = name ; param ; closure = { captured = defn ; env } }) in
      return (name, v)
    | SLet { var = VarTyped { item ; tau } ; defn } ->
      let* tval = eval_type tau in
      let* v = eval defn in
      let* l_opt = read_input make_label input_env in
      let check_t =
        let* () = push_and_log_label Check in
        check v tval
      in
      let cont =
        let* () = push_and_log_label Eval in
        (* TODO: wrap *)
        return (item, v)
      in
      begin match l_opt with
      | Some Check -> check_t
      | Some Eval -> cont
      | Some _ -> bad_input_env ()
      | None -> let* () = fork check_t in cont
      end
    | SLetRec { var = VarTyped { item ; tau } ; param ; defn } ->
      let* tval = eval_type tau in
      let* env = read in
      let* v =
        if do_splay then
          let* genned = gen tval in
          return_any (VFunClosure { param ; closure = { captured = defn ; env = Env.set item genned env }})
        else
          return_any (VFunFix { fvar = item ; param ; closure = { captured = defn ; env } })
      in
      let* l_opt = read_input make_label input_env in
      let check_t = 
        let* () = push_and_log_label Check in
        check v tval
      in
      let cont =
        let* () = push_and_log_label Eval in
        (* TODO: wrap *)
        return (item, v)
      in
      begin match l_opt with
      | Some Check -> check_t
      | Some Eval -> cont
      | Some _ -> bad_input_env ()
      | None -> let* () = fork check_t in cont
      end

  (*
    -------------------------------
    EVALUATE SYMBOLS TO WHNF VALUES
    -------------------------------

    TODO: instead of using a boolean to splay, have a functor that inserts the logic
      so we can statically avoid the branch.
  *)
  and force_eval (expr : Ast.t) : Cvalue.any m =
    let* v = eval expr in
    force_value v
  
  and force_value (v : Cvalue.any) : Cvalue.any m =
    if do_splay then
      match v with 
      | Any VLazy symbol ->
        let* lazy_v = find_symbol symbol in
        begin match lazy_v with
        | LGenMu { var ; closure } ->
          let* genned = force_gen_mu var closure in
          let* () = add_symbol symbol (LValue genned) in
          return genned
        | LGenList t ->
          let* genned = force_gen_list t in
          let* () = add_symbol symbol (LValue genned) in
          return genned
        | LValue v -> return v
        end
      | _ -> return v
    else
      (* without splaying, nothing is ever delayed because it adds incompleteness *)
      return v
  in



  let result, state = run (eval_statement_list pgm) target in
  let this_logged_run =
    Logged_run.{ target ; inputs = state.logged_inputs ; rev_stem = state.rev_stem }
  in
  result,
  Utils.Diff_list.(
    to_list @@ this_logged_run -:: state.runs
  )
