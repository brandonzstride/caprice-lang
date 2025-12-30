
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
  ~(default_int : unit -> int)
  ~(default_bool : unit -> bool)
  ~(do_splay : bool)
  ~(do_wrap : bool)
  : Answer.t * Logged_run.t list
  =
  (*
    Reads a tag from the input environment. If the tag was planned,
    then run the left or right accordingly (pushing the tag to this
    path).
    Otherwise, fork on the left and continue on the right.
  *)
  let fork_on_left (type a) ~(left : Eval_result.t failing) ~(right : a m) ~reason =
    let* l_opt = read_input make_tag input_env in
    match l_opt with
    | Some Left reason' when reason = reason' -> 
      let* () = push_and_log_tag @@ Left reason in
      left.run_failing
    | Some Right reason' when reason = reason' ->
      let* () = push_and_log_tag @@ Right reason in
      right
    | Some _ ->
      bad_input_env ()
    | None ->
      let* () = fork (
        let* () = push_and_log_tag @@ Left reason in
        left.run_failing
      ) in
      let* () = push_and_log_tag @@ Right reason in
      right
  in

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
      | Any (VFunClosure _ as vfun)
      | Any (VFunFix _ as vfun) ->
        let* v_arg = eval arg in
        eval_appl vfun v_arg
      | Any (VGenFun { domain ; _ } as vfun) ->
        let* v_arg = eval arg in
        fork_on_left ~reason:ApplGenFun
          ~left:{ run_failing = check v_arg domain }
          ~right:(eval_appl vfun v_arg)
      | Any (VWrapped { data ; tau } as self_fun) ->
        let* v_arg = eval arg in
        fork_on_left ~reason:ApplWrappedFun
          ~left:{ run_failing = check v_arg tau.domain }
          ~right:(
            let* tval =
              begin match tau.codomain with
              | CodValue tval -> return tval
              | CodDependent (id, { captured ; env }) ->
                local (fun _ -> Env.set id v_arg env) (eval_type captured)
              end
            in
            let* v_res = eval_appl ~self_fun data v_arg in
            wrap v_res tval
          )
      | _ -> mismatch @@ apply_non_function v_func
      end
    | EMatch { subject ; patterns } ->
      let* v = force_eval subject in
      let rec find_match = function
        | [] -> mismatch @@ missing_pattern v (List.map fst patterns)
        | (pat, body) :: tl ->
          let resolve_symbol symbol =
            force_value (Any (VLazy symbol))
          in
          let* res = Matches.match_any pat v ~resolve_symbol in
          begin match res with
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
      let* v2 = eval e2 in (* don't force eval because want to allow cons to lazy list *)
      begin match v2 with
      | Any (VEmptyList as tl)
      | Any (VListCons _ as tl) -> return_any (VListCons (v1, tl))
      | Any (VLazy symbol as tl) ->
        let* v_lazy = find_symbol symbol in
        begin match v_lazy with
        | LGenList _ -> 
          (* MAGIC: safe because lazy will evaluate to data eventually *)
          return_any (VListCons (v1, Obj.magic tl))
        | LValue Any (VEmptyList as tl)
        | LValue Any (VListCons _ as tl) -> return_any (VListCons (v1, tl))
        | _ -> mismatch @@ cons_non_list v1 v2
        end
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
    let eval_short_circuit vleft =
      match vleft with
      | Any VBool (b, s) when (not b && op = BAnd) || (b && op = BOr) ->
        (* Cases here are: false AND rhs, true OR rhs *)
        (* The short-circuiting is effectively a branch, so log the formula *)
        let* () = push_formula (Smt.Formula.binop Equal s (Smt.Formula.const_bool b)) in
        return vleft
      | Any VBool (b, s) ->
        (* Need to evaluate RHS here *)
        let* () = push_formula (Smt.Formula.binop Equal s (Smt.Formula.const_bool b)) in
        let* vright = force_eval right in
        begin match vright with
        | Any VBool _ -> return vright
        | _ -> mismatch @@ bad_binop vleft op vright
        end
      | _ -> mismatch @@ bad_binop vleft op (Any VUnit) (* placeholder because there is no expr printing yet *)
    in
    match op with
    | BAnd | BOr -> eval_short_circuit vleft
    | _ ->
      let* vright = force_eval right in
      let fail_binop () = (* delay this so as not to eagerly construct the string *)
        mismatch @@ bad_binop vleft op vright in
      let k f s1 s2 op =
        return_any @@ f (Smt.Formula.binop op s1 s2)
      in
      let v_int n s = VInt (n, s) in
      let v_bool n s = VBool (n, s) in
      match op, vleft, vright with
      | BPlus       , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_int (n1 + n2)) e1 e2 Plus
      | BMinus      , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_int (n1 - n2)) e1 e2 Minus
      | BTimes      , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_int (n1 * n2)) e1 e2 Times
      | BEqual      , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_bool (n1 = n2)) e1 e2 Equal
      | BEqual      , Any VBool (b1, e1), Any VBool (b2, e2) -> k (v_bool (b1 = b2)) e1 e2 Equal
      | BNeq        , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_bool (n1 <> n2)) e1 e2 Not_equal
      | BLessThan   , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_bool (n1 < n2)) e1 e2 Less_than
      | BLeq        , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_bool (n1 <= n2)) e1 e2 Less_than_eq
      | BGreaterThan, Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_bool (n1 > n2)) e1 e2 Greater_than
      | BGeq        , Any VInt (n1, e1) , Any VInt (n2, e2)  -> k (v_bool (n1 >= n2)) e1 e2 Greater_than_eq
      | BDivide, Any VInt (n1, e1), Any VInt (n2, e2) when n2 <> 0 ->
        let* () = push_formula (Smt.Formula.binop Not_equal e2 (Smt.Formula.const_int 0)) in
        k (v_int (n1 / n2)) e1 e2 Divide
      | BModulus, Any VInt (n1, e1), Any VInt (n2, e2) when n2 <> 0 ->
        let* () = push_formula (Smt.Formula.binop Not_equal e2 (Smt.Formula.const_int 0)) in
        k (v_int (n1 mod n2)) e1 e2 Modulus
      | BTimes, Any v1, Any v2 ->
        (* Make tuple if v1 and v2 are types. Note that integer muliplication is handled above. *)
        handle v1
          ~typeval:(fun t1 ->
            handle v2
              ~typeval:(fun t2 -> return_any @@ VTypeTuple (t1, t2))
              ~data:(fun _ -> fail_binop ())
          )
          ~data:(fun _ -> fail_binop ())
      | _ -> fail_binop ()

  (*
    ---------------------
    EVALUATE APPLICATIONS
    ---------------------

    Always takes the evaluation side. Does not do any checking.
    Does not push any labels corresponding to the evaluation.
    Does not wrap the result.

    ?self_fun is the optional value to put in the environment as
    the self for recursive functions, in case of wrapping.
    The default value is the actual fixed function.
  *)
  and eval_appl (v_func : Cvalue.dval) ?(self_fun : Cvalue.dval = v_func) (v_arg : Cvalue.any) : Cvalue.any m =
    match v_func with
    | VFunClosure { param ; closure = { captured ; env } } ->
      local (fun _ -> Env.set param v_arg env) (eval captured)
    | VFunFix { fvar ; param ; closure = { captured ; env } } ->
      if do_splay then fail (Mismatch "Called rec fun while splaying") else
      local (fun _ -> 
        Env.set fvar (Any self_fun) env
        |> Env.set param v_arg
      ) (eval captured)
    | VGenFun { domain = _ ; codomain } ->
      begin match codomain with
      | CodValue cod_tval -> gen cod_tval
      | CodDependent (id, { captured ; env }) ->
        let* cod_tval = local (fun _ -> Env.set id v_arg env) (eval_type captured) in
        gen cod_tval
      end
    | _ -> mismatch @@ apply_non_function (Any v_func)
    
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
        | CodDependent (id, { captured ; env }) ->
          let* cod_tval = local (fun _ -> Env.set id genned env) (eval_type captured) in
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
        fork_on_left ~reason:CheckGenFun
          ~left:{ run_failing =
            if domain = domain' then confirm else
            let* genned = gen domain in
            check genned domain'
          }
          ~right:(
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
          )
      | Any VWrapped { data ; _ } ->
        check (Any data) t (* FIXME: actually consider the wrapping type *)
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
            let* () = push_and_log_tag (Interp.Tag.of_record_label label) in
            check
              (Labels.Record.Map.find label record_v)
              (Labels.Record.Map.find label record_t)
          in
          let* l_opt = read_input make_tag input_env in
          match l_opt with
          | Some Label id -> push_and_check (Labels.Record.RecordLabel id)
          | Some _ -> bad_input_env ()
          | None ->
            (* is in exploration mode, so we want to check them all *)
            begin match Labels.Record.Set.random_opt t_labels with
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
    | VTypeList t_body ->
      begin match v with
      | Any VLazy s ->
        let* lazy_v = find_symbol s in
        begin match lazy_v with
        | LValue v -> check v t
        | LGenMu _ -> refute (* see mu todo *)
        | LGenList t' ->
          if t' = t_body then confirm else
          let* genned = gen t' in
          check genned t_body
        end
      | Any VEmptyList -> confirm
      | Any VListCons (v_hd, v_tl) ->
        fork_on_left ~reason:CheckList
          ~left:{ run_failing = check v_hd t_body }
          ~right:(check (Any v_tl) t)
      | _ -> refute
      end
    | VTypeRefine { var ; tau ; predicate = { captured ; env } } ->
      (* Value is not directly used here, so we don't force it *)
      fork_on_left ~reason:CheckRefinementType
        ~left:{ run_failing = check v tau }
        ~right:(
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
        )
    | VTypeTuple (t1, t2) ->
      let* v = force_value v in
      begin match v with
      | Any VTuple (v1, v2) ->
        fork_on_left ~reason:CheckTuple
          ~left:{ run_failing = check v1 t1 }
          ~right:(check v2 t2)
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
            let* () = push_and_log_tag (Interp.Tag.of_record_label label) in
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
          let* l_opt = read_input make_tag input_env in
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
          fork_on_left ~reason:CheckSingletype
            ~left:{ run_failing =
              (* check subset *)
              let* genned = gen tval' in
              check genned tval
            }
            ~right:(
              (* check superset *)
              let* genned = gen tval in
              check genned tval'
            )
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
      let* i = read_and_log_input_with_default make_int input_env ~default:(default_int ()) in
      return_any (VInt (i, Stepkey.int_symbol step))
    | VTypeBool ->
      let* step = step in
      let* b = read_and_log_input_with_default make_bool input_env ~default:(default_bool ()) in
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
        read_and_log_input_with_default make_tag input_env
          ~default:(default_constructor variant_t |> Interp.Tag.of_variant_label)
      in
      begin match l with
      | Label id ->
        let to_gen = Labels.Variant.of_ident id in
        let t = Labels.Variant.Map.find to_gen variant_t in
        let* () =
          push_tag Interp.Tag.With_alt.{ main = l ; alts =
            Labels.Variant.Set.remove to_gen t_labels
            |> Labels.Variant.Set.to_list
            |> List.map Interp.Tag.of_variant_label
          }
        in
        let* payload = gen t in
        return_any (VVariant { label = to_gen ; payload })
      | _ -> bad_input_env ()
      end
    | VTypeList t ->
      if do_splay then
        make_new_lazy_value (LGenList t)
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
      if do_splay then
        make_new_lazy_value (LGenMu { var ; closure })
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
    let* l = read_and_log_input_with_default make_tag input_env ~default:(Left GenList) in
    match l with
    | Left GenList ->
      let* () = push_tag Interp.Tag.With_alt.{ main = Left GenList ; alts = [ Right GenList ] } in
      return_any VEmptyList
    | Right GenList ->
      let* () = push_tag Interp.Tag.With_alt.{ main = Right GenList ; alts = [ Left GenList ] } in
      let* hd = gen body in
      let* Any tl = gen (VTypeList body) in
      (* MAGIC: Safe because always returns data, even though lazily generated list is technically "neither" *)
      return_any (VListCons (hd, Obj.magic tl))
    | _ -> bad_input_env ()

  and force_gen_mu (var : Ident.t) (closure : Ast.t Cvalue.closure) : Cvalue.any m =
    let* t_body = 
      local (fun _ -> Env.set var (Any (VTypeMu { var ; closure })) closure.env) 
        (eval_type closure.captured)
    in
    gen t_body

  and wrap (v : Cvalue.any) (t : Cvalue.tval) : Cvalue.any m =
    if not do_wrap then return v else
    match t with
    | VType
    | VTypePoly _
    | VTypeUnit
    | VTypeTop
    | VTypeInt
    | VTypeBool
    | VTypeSingle _ -> return v
    | VTypeBottom -> fail @@ Mismatch "Cannot wrap with bottom"
    | VTypeMu { var ; closure = { captured ; env } } ->
      (* TODO: handle splaying *)
      let* tval = local (fun _ -> Env.set var (Any t) env) (eval_type captured) in
      wrap v tval
    | VTypeList t_body ->
      (* TODO: handle splaying *)
      begin match v with
      | Any VEmptyList -> return v
      | Any VListCons (v_hd, v_tl) ->
        let* w_hd = wrap v_hd t_body in
        let* Any w_tl = wrap (Any v_tl) t in
        return_any (VListCons (w_hd, Obj.magic w_tl))
      | _ -> fail @@ Mismatch "Wrap non-list with list type"
      end
    | VTypeFun tfun ->
      begin match v with
      | Any VWrapped { data ; tau = _ } -> return_any (VWrapped { data ; tau = tfun })
      | Any v' ->
        handle v'
          ~data:(fun data -> return_any (VWrapped { data ; tau = tfun }))
          ~typeval:(fun _ -> fail @@ Mismatch "Wrap non-data with function type")
      end
    | VTypeRecord t_body ->
      begin match v with
      | Any VRecord v_body ->
        let* w_body =
          Labels.Record.Map.fold (fun k t acc_m ->
            let* acc = acc_m in
            match Labels.Record.Map.find_opt k v_body with
            | Some v' -> 
              let* w = wrap v' t in
              return (Labels.Record.Map.add k w acc)
            | None -> fail @@ Mismatch "Wrap missing record label"
          ) t_body (return Labels.Record.Map.empty)
        in
        return_any (VRecord w_body)
      | _ -> fail @@ Mismatch "Wrap non-record"
      end
    | VTypeModule { captured = t_ls ; env } ->
      begin match v with
      | Any VModule v_body ->
        let rec fold_labels acc_m = function
          | [] -> acc_m
          | { Ast.item ; tau } :: tl ->
            let* acc = acc_m in
            begin match Labels.Record.Map.find_opt item v_body with
            | Some v' ->
              let* tval = eval_type tau in
              let* v = wrap v' tval in
              local (Env.set (Labels.Record.to_ident item) v) (
                fold_labels (return @@ Labels.Record.Map.add item v acc) tl
              )
            | None ->
              fail @@ Mismatch "Wrap missing module label"
            end
        in
        let* wrapped_body =
          local (fun _ -> env) (
            fold_labels (return Labels.Record.Map.empty) t_ls
          )
        in
        return_any (VModule wrapped_body)
      | _ -> fail @@ Mismatch "Wrap non-module"
      end
    | VTypeVariant t_body ->
      begin match v with
      | Any VVariant { label ; payload } ->
        begin match Labels.Variant.Map.find_opt label t_body with
        | Some t ->
          let* w = wrap payload t in
          return_any (VVariant { label ; payload = w })
        | None -> 
          fail @@ Mismatch "Wrap missing variant label"
        end
      | _ -> fail @@ Mismatch "Wrap non-variant"
      end
    | VTypeTuple (t1, t2) ->
      begin match v with
      | Any VTuple (v1, v2) ->
        let* w1 = wrap v1 t1 in
        let* w2 = wrap v2 t2 in
        return_any (VTuple (w1, w2))
      | _ -> fail @@ Mismatch "Wrap non-tuple"
      end
    | VTypeRefine { var = _ ; tau ; predicate = _ } ->
      wrap v tau

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
      fork_on_left ~reason:CheckLetExpr
        ~left:{ run_failing = check v tval }
        ~right:(
          let* w = wrap v tval in
          return (item, w)
        )
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
      fork_on_left ~reason:CheckLetExpr
        ~left:{ run_failing = check v tval }
        ~right:(
          let* w = wrap v tval in
          return (item, w)
        )

  (*
    -------------------------------
    EVALUATE SYMBOLS TO WHNF VALUES
    -------------------------------
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
      (* without splaying, nothing is ever delayed because it would be incomplete *)
      return v
  in

  let result, state = run (eval_statement_list pgm) target in
  let answer = Eval_result.to_answer result in
  let this_logged_run =
    { Logged_run.target 
    ; inputs = state.logged_inputs 
    ; rev_stem = state.rev_stem
    ; answer }
  in
  answer,
  Utils.Diff_list.(
    to_list @@ this_logged_run -:: state.runs
  )
