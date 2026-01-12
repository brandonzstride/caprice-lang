
open Lang
open Effects
open Grammar
open Grammar.Val

(* `Any` is unboxed, so this is zero overhead *)
let[@inline always] return_any v = return (Any v)

let bad_input_env : 'a. unit -> 'a = fun () ->
  raise @@ InvariantException "Input environment is ill-formed"

let make_lazy (lgen : Val.lgen) : Val.dval =
  VLazy { cell = State.make_cell (LLazy lgen) ; wrapping_types = [] }

open Grammar.Val.Error_messages
open Input_env.Key

let eval
  (pgm : Ast.statement list)
  (input_env : Input_env.t)
  (target : Target.t)
  ~(max_step : Grammar.Step.t)
  ~(default_int : unit -> int)
  ~(default_bool : unit -> bool)
  ~(do_splay : bool)
  ~(do_wrap : bool)
  : Answer.t * Logged_run.t list
  =
  let read_and_log_bool () =
    read_and_log_input_with_default make_bool input_env ~default:(default_bool ())
  in

  let read_and_log_int () =
    read_and_log_input_with_default make_int input_env ~default:(default_int ())
  in

  (*
    Reads a tag from the input environment. If the tag was planned,
    then run the left or right accordingly (pushing the tag to this
    path).
    Otherwise, fork on the left and continue on the right.
  *)
  let fork_on_left (type a env) ~(left : (Eval_result.t, env) failing) ~(right : (a, env) m) ~reason =
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

    Uses the environment, so the type parameter for the environment in
    the monad is instantiated with Val.Env.t.
  *)
  let rec eval (expr : Ast.t) : (Val.any, Val.Env.t) m =
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
      | Any (VGenFun { funtype = { domain ; _ } ; _ } as vfun) ->
        let* v_arg = eval arg in
        fork_on_left ~reason:ApplGenFun
          ~left:{ run_failing = check v_arg domain }
          ~right:(eval_appl vfun v_arg)
      | Any (VWrapped { data ; tau } as self_fun) ->
        let* v_arg = eval arg in
        fork_on_left ~reason:ApplWrappedFun
          ~left:{ run_failing = check v_arg tau.domain }
          ~right:(
            let* v_res = eval_appl ~self_fun data v_arg in
            let* tval = eval_codomain tau.codomain v_arg in
            wrap v_res tval
          )
      | _ -> mismatch @@ apply_non_function v_func
      end
    | EMatch { subject ; patterns } ->
      let* v = force_eval subject in
      let rec find_match = function
        | [] -> mismatch @@ missing_pattern v (List.map fst patterns)
        | (pat, body) :: tl ->
          let* res = Matches.match_any pat v ~resolve_lazy in
          begin match res with
          | Match -> eval body
          | Match_bindings e -> local (fun env -> Env.extend env e) (eval body)
          | No_match -> find_match tl
          | Failure msg -> escape (Mismatch msg)
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
      let cons_with_v1 tl = return_any (VListCons (v1, tl)) in
      begin match v2 with
      | Any (VEmptyList as tl)
      | Any (VListCons _ as tl) -> cons_with_v1 tl
      | Any (VLazy { cell ; _ } as tl) ->
        let v_lazy = State.get_cell cell in
        begin match v_lazy with
        | LLazy LGenList _
        | LValue Any VEmptyList
        | LValue Any VListCons _ -> cons_with_v1 tl
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
      let* i = read_and_log_int () in
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
          escape Assert_false
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
          escape Vanish
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
    | ETypeFun { domain = PReg { tau } ; codomain ; sort } ->
      let* dom_t = eval_type tau in
      let* cod_t = eval_type codomain in
      return_any (VTypeFun { domain = dom_t ; codomain = CodValue cod_t ; sort })
    | ETypeFun { domain = PDep { item ; tau } ; codomain ; sort } ->
      let* dom_t = eval_type tau in
      let* env = read in
      return_any (VTypeFun { domain = dom_t ; codomain = CodDependent (item, { captured = codomain ; env }) ; sort })
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

    Uses environment during evaluation.
  *)
  and eval_binop (left : Ast.t) (op : Binop.t) (right : Ast.t) : (Val.any, Val.Env.t) m =
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
    Does not wrap the result. Does not accept wrapped values as
    function to apply.

    ?self_fun is the optional value to put in the environment as
    the self for recursive functions, in case of wrapping.
    The default value is the actual fixed function.

    This does not use a monadic environment, so the environment is
    universally quantified.
  *)
  and eval_appl 
    : 'env. Val.dval -> ?self_fun:Val.dval -> Val.any -> (Val.any, 'env) m
    = fun v_func ?(self_fun = v_func) v_arg ->
    match v_func with
    | VFunClosure { param ; closure = { captured ; env } } ->
      local' (Env.set param v_arg env) (eval captured)
    | VFunFix { fvar ; param ; closure = { captured ; env } } ->
      if do_splay && is_any_symbolic v_arg then
        mismatch (
          Format.sprintf "Called rec fun with symbolic value %s while splaying"
            (Val.any_to_string v_arg)
          )
      else
        local' (
          Env.set fvar (Any self_fun) env
          |> Env.set param v_arg
        ) (eval captured)
    | VGenFun { funtype = { domain = _ ; codomain ; sort = Nondet } ; _ } ->
      let* cod_tval = eval_codomain codomain v_arg in
      gen cod_tval
    | VGenFun { funtype = { domain = _ ; codomain ; sort = Det } ; alist ; _ } ->
      let rec loop = function
        | [] ->
          let* cod_tval = eval_codomain codomain v_arg in
          let* genned = gen cod_tval in
          State.set_cell alist ((v_arg, genned) :: State.get_cell alist);
          return genned
        | (input, output) :: tl ->
          begin match Val.intensional_equal v_arg input with
          | Value (true, s) ->
            let* () = push_formula s in
            return output
          | Value (false, s) ->
            let* () = push_formula (Formula.not_ s) in
            loop tl
          | SortMismatch ->
            mismatch "Sort mismatch in intensional equality"
          end
      in
      loop (State.get_cell alist)
    | _ -> mismatch @@ apply_non_function (Any v_func)
    
  (*
    ---------------------------------
    EVALUATE EXPRESSION TO TYPE VALUE
    ---------------------------------

    Uses environment to evaluate.
  *)
  and eval_type (expr : Ast.t) : (Val.tval, Val.Env.t) m =
    let* v = force_eval expr in
    handle_any v
      ~data:(fun d -> mismatch @@ non_type_value d)
      ~typeval:return

  (*
    --------------------------
    EVALUATE FUNCTION CODOMAIN
    --------------------------

    Given a witness value of the domain type, evaluate the codomain
    (whether it is already a type value or it depends on the witness)
    to a type value.

    Does not use environment.
  *)
  and eval_codomain
    : 'env. Val.fun_cod -> Val.any -> (Val.tval, 'env) m
    = fun cod dom_witness ->
    match cod with
    | CodValue cod_tval ->
      return cod_tval
    | CodDependent (id, { captured ; env }) ->
      local' (Env.set id dom_witness env) (eval_type captured)

  (*
    -------------------------
    CHECK FOR TYPE REFUTATION
    -------------------------

    Does not use environment.
  *)
  and check
    : type a env. Val.any -> Val.tval -> (a, env) m
    = fun v t ->
    let refute = escape (Refutation (v, t)) in
    let confirm = escape Confirmation in
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
    | VTypeTop -> (* don't force v *)
      (* Everything is in top *)
      confirm
    | VTypeBottom -> (* don't force v *)
      (* Nothing is in bottom *)
      refute
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
    | VTypeFun { domain ; codomain ; sort = _ } ->
      let* v = force_value v in
      begin match v with
      | Any (VFunClosure _ as vfun)
      | Any (VFunFix _ as vfun) ->
        (* TODO: if sort is deterministic, check that this evaluates deterministically *)
        let* genned = gen domain in
        let* res = eval_appl vfun genned in
        let* cod_tval = eval_codomain codomain genned in
        check res cod_tval
      | Any (VGenFun { funtype = { domain = domain' ; codomain = codomain' ; sort = sort' } ; _ } as v_candidate) ->
        fork_on_left ~reason:CheckGenFun
          ~left:{ run_failing = domain <: domain' }
          ~right:(
            if Val.equal_fun_cod codomain codomain' then confirm else
            match sort' with
            | Nondet ->
              let* cod_tval, cod_tval' =
                match codomain, codomain' with
                | CodValue cod_tval, CodValue cod_tval' -> 
                  return (cod_tval, cod_tval')
                | _ ->
                  let* genned = gen domain in
                  let* cod_tval = eval_codomain codomain genned in
                  let* cod_tval' = eval_codomain codomain' genned in
                  return (cod_tval, cod_tval')
              in
              cod_tval' <: cod_tval
            | Det ->
              let* v_arg = gen domain in
              let* res = eval_appl v_candidate v_arg in
              let* cod_tval = eval_codomain codomain v_arg in
              check res cod_tval
          )
      | Any (VWrapped { data ; tau = { domain = domain' ; codomain = codomain' ; sort = _ } } as self_fun) ->
        fork_on_left ~reason:CheckWrappedFun
          ~left:{ run_failing = domain <: domain' }
          ~right:(
            (*
              The left has already checked the domain, so we can assume the 
              domain side is well-typed.

              We can skip the work on the right if the codomains are equal
                because the wrapper means its been checked.
            *)
            if Val.equal_fun_cod codomain codomain' then confirm else
            (* TODO: remove this duplication with all the above cases
              (this is almost just the "right" side of checking functions but
              with wrapping the result in the wrapping codomain'). *)
            match data with
            | VFunClosure _
            | VFunFix _ ->
              let* genned = gen domain in
              let* cod_tval = eval_codomain codomain genned in (* note og codomain uses unwrapped value *)
              let* w = wrap genned domain' in
              let* res = eval_appl data ~self_fun genned in
              let* cod_tval' = eval_codomain codomain' w in
              let* w_res = wrap res cod_tval' in
              check w_res cod_tval
            | VGenFun { funtype = { domain = _ ; codomain = codomain'' ; sort = Nondet } ; _ } ->
              let* cod_tval, cod_tval', cod_tval'' =
                match codomain, codomain', codomain'' with
                | CodValue cod_tval, CodValue cod_tval', CodValue cod_tval'' -> 
                  return (cod_tval, cod_tval', cod_tval'')
                | _ ->
                  let* genned = gen domain in
                  let* cod_tval = eval_codomain codomain genned in
                  let* w = wrap genned domain' in
                  let* cod_tval' = eval_codomain codomain' w in
                  let* cod_tval'' = eval_codomain codomain'' w in (* TODO: should this "w" be wrapped with domain''? *)
                  return (cod_tval, cod_tval', cod_tval'')
              in
              if Val.equal cod_tval cod_tval'' then confirm else
              let* genned = gen cod_tval'' in
              let* w = wrap genned cod_tval' in
              check w cod_tval
            | VGenFun { funtype = { domain = domain'' ; codomain = _ ; sort = Det } ; _ } ->
              fork_on_left ~reason:CheckGenFun
                ~left:{ run_failing = domain <: domain'' }
                ~right:(
                  if Val.equal_fun_cod codomain codomain' then confirm else
                  let* v_arg = gen domain in
                  let* w_arg = wrap v_arg domain' in
                  let* res = eval_appl data w_arg in
                  let* cod_tval = eval_codomain codomain v_arg in
                  check res cod_tval
                )
            | _ -> refute
          )
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
          let push_and_check label =
            { run_failing =
              (* alternatives do not matter when we are running every label right now *)
              let* () = push_and_log_tag (Grammar.Tag.of_record_label Check label) in
              check
                (Labels.Record.Map.find label record_v)
                (Labels.Record.Map.find label record_t)
            }
          in
          check_struct push_and_check ~refute ~t_labels ~v_labels
      | _ -> refute
      end
    | VTypeModule { captured ; env } ->
      let* v = force_value v in
      begin match v with
      | Any VModule module_v ->
        let t_labels_ls = List.map (fun { Ast.item ; _ } -> item) captured in
        let t_labels = Labels.Record.Set.of_list t_labels_ls in
        let v_labels = Record.label_set module_v in
        let push_and_check label =
          { run_failing =
            (* alternatives do not matter when we are running every label right now *)
            let* () = push_and_log_tag (Grammar.Tag.of_record_label Check label) in
            let new_env, tau = 
              (* think about sharing this computation because rn it is redone on every fork *)
              Utils.List_utils.fold_left_until (fun env { Ast.item = label' ; tau } ->
                if Labels.Record.equal label' label
                then `Stop (env, tau)
                else `Continue (
                  Env.set (Labels.Record.to_ident label') (Labels.Record.Map.find label' module_v) env
                )
              ) (fun _ -> raise @@ InvariantException "Label not found in module type") env captured
            in
            let* t = local' new_env (eval_type tau) in
            check (Labels.Record.Map.find label module_v) t
          }
        in
        check_struct push_and_check ~refute ~t_labels ~v_labels
      | _ -> refute
      end
    | VTypeMu { var ; closure = { captured ; env } } -> (* don't force v *)
      begin match v with
      | Any VLazy { cell ; wrapping_types } ->
        let lazy_v = State.get_cell cell in
        begin match lazy_v with
        | LValue any_v ->
          check any_v t
        | LLazy LGenList _ ->
          refute (* TODO: make error message description; it will be cryptic like this *)
        | LLazy LGenMu { var = var' ; closure = { captured = captured' ; env = env' } } ->
          (* TODO: these names (with the "prime") go the other direction as the spec *)
          (* FIXME: consider wrapping_types. *)
          if Val.equal_closure { captured ; env } { captured = captured' ; env = env' }
              && wrapping_types = [] then confirm else
          let* a = gen VType in (* fresh type to use as a stub *)
          let* t_body = local' (Env.set var a env) (eval_type captured) in
          let* t_body' = local' (Env.set var' a env') (eval_type captured') in
          (* we would need to address the fixme by wrapping the generated
            member inside the call to (<:) *)
          t_body' <: t_body
        end
      | _ ->
        let* t_body = local' (Env.set var (Any t) env) (eval_type captured) in
        check v t_body
      end
    | VTypeList t_body -> (* don't force v *)
      begin match v with
      | Any VLazy { cell ; wrapping_types } ->
        let lazy_v = State.get_cell cell in
        begin match lazy_v with
        | LValue any_v ->
          let* wrapped = wrap_multi wrapping_types any_v in
          check wrapped t
        | LLazy LGenMu _ ->
          refute (* see todo on mu check about error messages *)
        | LLazy LGenList t' ->
          if wrapping_types = [] && Val.equal t' t_body then confirm else
          let* genned = gen t' in
          (* genned is only a single element of the list, so wrap it
            by extracting the type bodies out of the list type *)
          let* wrapping_bodies =
            List.fold_right (fun twrap acc_m ->
              let* acc = acc_m in
              match twrap with
              | VTypeList tval -> return (tval :: acc)
              | _ -> mismatch "Wrap list with non-list type"
            ) wrapping_types (return [])
          in
          let* wrapped = wrap_multi wrapping_bodies genned in
          check wrapped t_body
        end
      | Any VEmptyList -> confirm
      | Any VListCons (v_hd, v_tl) ->
        fork_on_left ~reason:CheckList
          ~left:{ run_failing = check v_hd t_body }
          ~right:(check (Any v_tl) t)
      | _ -> refute
      end
    | VTypeRefine { var ; tau ; predicate = { captured ; env } } ->
      (* Value is not directly used here, so we don't force it quite yet *)
      fork_on_left ~reason:CheckRefinementType
        ~left:{ run_failing = check v tau }
        ~right:(
          let* p = local' (Env.set var v env) (eval captured) in
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
    | VTypeSingle tval ->
      let* v = force_value v in
      handle_any v
        ~data:(fun _ -> refute)
        ~typeval:(fun tval' ->
          if Val.equal tval' tval then confirm else
          fork_on_left ~reason:CheckSingletype
            ~left:{ run_failing = tval' <: tval }
            ~right:(tval <: tval')
        )

  (*
    Check modules and records given a way to check each label and a default
    label
  *)
  and check_struct
    : type a env. (Labels.Record.t -> (Eval_result.t, env) failing) -> refute:(a, env) m ->
      t_labels:Labels.Record.Set.t -> v_labels:Labels.Record.Set.t -> (a, env) m
    = fun check_label ~refute ~t_labels ~v_labels ->
      if Labels.Record.Set.subset t_labels v_labels then
        let* l_opt = read_input make_tag input_env in
        match l_opt with
        | Some Label (id, Check) -> (check_label (Labels.Record.RecordLabel id)).run_failing
        | Some _ -> bad_input_env ()
        | None ->
          (* is in exploration mode, so we want to check every label *)
          let rec go = function
            | [] -> escape Confirmation
            | label :: tl ->
              let* () = fork (check_label label).run_failing in
              go tl
          in
          go (Labels.Record.Set.to_list t_labels)
      else
        refute

  (*
    -------------
    CHECK SUBTYPE
    -------------

    [t1 <: t2] can be a refutation if t1 is not
      a subtype of t2. It is a confirmation on failure to
      find such refutation.

    Does not use the environment.
  *)
  and (<:)
    : 'a 'env. Val.tval -> Val.tval -> ('a, 'env) m
    = fun t1 t2 ->
      if Val.equal t1 t2 then
        escape Confirmation
      else
        let* genned = gen t1 in
        check genned t2

  (*
    -------------------------
    GENERATE MEMBER OF A TYPE
    -------------------------

    Does not use the environment.
  *)
  and gen 
    : 'env. Val.tval -> (Val.any, 'env) m
    = fun t ->
    let* () = incr_step ~max_step in
    match t with
    | VTypeUnit ->
      return_any VUnit
    | VTypeInt ->
      let* step = step in
      let* i = read_and_log_int () in
      return_any (VInt (i, Stepkey.int_symbol step))
    | VTypeBool ->
      let* step = step in
      let* b = read_and_log_bool () in
      return_any (VBool (b, Stepkey.bool_symbol step))
    | VTypeFun funtype ->
      let* Step nonce = step in
      return_any (VGenFun { funtype ; nonce ; alist = State.make_cell [] })
    | VType ->
      let* Step id = step in (* will use step for a fresh integer *)
      return_any (VTypePoly { id })
    | VTypePoly { id } ->
      let* Step nonce = step in (* will use step for a fresh nonce *)
      return_any (VGenPoly { id ; nonce })
    | VTypeTop ->
      (* parametric polymorphism is enough here *)
      let* newtype = gen VType in
      handle_any newtype
        ~data:(fun _ -> raise @@ InvariantException "`type` generated data value")
        ~typeval:(fun typ -> gen typ)
    | VTypeBottom -> escape Vanish
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
          ~default:(default_constructor variant_t |> Grammar.Tag.of_variant_label Gen)
      in
      begin match l with
      | Label (id, Gen) ->
        let to_gen = Labels.Variant.of_ident id in
        let t = Labels.Variant.Map.find to_gen variant_t in
        let* () =
          push_tag Grammar.Tag.With_alt.{ main = l ; alts =
            Labels.Variant.Set.remove to_gen t_labels
            |> Labels.Variant.Set.to_list
            |> List.map (Grammar.Tag.of_variant_label Gen)
          }
        in
        let* payload = gen t in
        return_any (VVariant { label = to_gen ; payload })
      | _ -> bad_input_env ()
      end
    | VTypeList t ->
      if do_splay then
        return_any (make_lazy (LGenList t))
      else
        force_gen_list t
    | VTypeRefine { var ; tau ; predicate = { captured ; env } } ->
      let* v = gen tau in
      let* p = local' (Env.set var v env) (eval captured) in
      begin match p with
      | Any VBool (true, s) ->
        let* () = push_formula ~allow_flip:false s in
        return v
      | Any VBool (false, s) ->
        let* () = push_formula (Smt.Formula.not_ s) in
        escape Vanish
      | _ -> mismatch @@ non_bool_predicate p
      end 
    | VTypeMu { var ; closure } ->
      if do_splay then
        return_any (make_lazy (LGenMu { var ; closure }))
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
        local' env (
          fold_labels (return Labels.Record.Map.empty) captured
        )
      in
      return_any (VModule genned_body)
    | VTypeSingle tval ->
      return_any tval

  (*
    Generate a list. Makes an actual list instead of a symbol for a lazy one.

    Does not use the environment.
  *)
  and force_gen_list 
    : 'env. Val.tval -> (Val.any, 'env) m
    = fun body ->
    let* l = read_and_log_input_with_default make_tag input_env ~default:(Left GenList) in
    match l with
    | Left GenList ->
      let* () = push_tag Grammar.Tag.With_alt.{ main = Left GenList ; alts = [ Right GenList ] } in
      let* () = incr_step ~max_step in (* doesn't call gen, so need to increment step manually *)
      return_any VEmptyList
    | Right GenList ->
      let* () = push_tag Grammar.Tag.With_alt.{ main = Right GenList ; alts = [ Left GenList ] } in
      let* hd = gen body in
      let* Any v_tl = gen (VTypeList body) in
      handle v_tl
        ~data:(fun tl -> return_any @@ VListCons (hd, tl))
        ~typeval:(fun _ -> raise @@ InvariantException "List generation makes a type value")
    | _ -> bad_input_env ()

  (*
    Generate a member of a recursive type. Does not make a symbol for a lazy member.

    Does not use the environment.
  *)
  and force_gen_mu 
    : 'env. Ident.t -> Ast.t Val.closure -> (Val.any, 'env) m
    = fun var closure ->
    let* t_body = 
      local' (Env.set var (Any (VTypeMu { var ; closure })) closure.env) 
        (eval_type closure.captured)
    in
    gen t_body

  (*
    ----
    WRAP
    ----

    Does not use the environment.
  *)
  and wrap 
    : 'env. Val.any -> Val.tval -> (Val.any, 'env) m
    = fun v t ->
    if not do_wrap then return v else
    match t with
    | VType
    | VTypePoly _
    | VTypeUnit
    | VTypeTop
    | VTypeInt
    | VTypeBool
    | VTypeSingle _ -> return v
    | VTypeBottom -> mismatch @@ wrap_bottom v
    | VTypeMu { var ; closure = { captured ; env } } ->
      let* tval = local' (Env.set var (Any t) env) (eval_type captured) in
      begin match v with
      | Any VLazy vlazy ->
        (* Always lazily wrap, even if the value is forced already. *)
        (* It is safe to put this off because any error when wrapping would be an
          error when checking, which is already done eagerly. *)
        if does_wrap_matter tval then
          return_any (VLazy { vlazy with wrapping_types = tval :: vlazy.wrapping_types })
        else
          return v
      | _ -> 
        wrap v tval
      end
    | VTypeList t_body ->
      begin match v with
      | Any VLazy vlazy ->
        if does_wrap_matter t then
          return_any (VLazy { vlazy with wrapping_types = t :: vlazy.wrapping_types })
        else
          return v
      | Any VEmptyList ->
        return v
      | Any VListCons (v_hd, v_tl) ->
        let* w_hd = wrap v_hd t_body in
        let* Any w_tl = wrap (Any v_tl) t in
        handle w_tl
          ~data:(fun w_tl_data -> return_any (VListCons (w_hd, w_tl_data)))
          ~typeval:(fun _ -> raise @@ InvariantException "Wrapped list is not data")
      | _ -> mismatch @@ wrap_non_list v t
      end
    | VTypeFun tfun ->
      begin match v with
      | Any VWrapped { data ; tau = _ } -> return_any (VWrapped { data ; tau = tfun })
      | Any v' ->
        handle v'
          ~data:(fun data -> return_any (VWrapped { data ; tau = tfun }))
          ~typeval:(fun t' -> mismatch @@ wrap_typeval_fun t' t)
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
            | None -> mismatch @@ wrap_missing_label v k
          ) t_body (return Labels.Record.Map.empty)
        in
        return_any (VRecord w_body)
      | _ -> mismatch @@ wrap_non_record v t
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
              mismatch @@ wrap_missing_label v item
            end
        in
        let* wrapped_body =
          local' env (
            fold_labels (return Labels.Record.Map.empty) t_ls
          )
        in
        return_any (VModule wrapped_body)
      | _ -> mismatch @@ wrap_non_module v t
      end
    | VTypeVariant t_body ->
      begin match v with
      | Any VVariant { label ; payload } ->
        begin match Labels.Variant.Map.find_opt label t_body with
        | Some t ->
          let* w = wrap payload t in
          if w == payload then
            return v (* return value unchanged because wrapping did nothing *)
          else
            return_any (VVariant { label ; payload = w })
        | None -> 
          mismatch @@ wrap_missing_constructor v t
        end
      | _ -> mismatch @@ wrap_non_variant v t
      end
    | VTypeTuple (t1, t2) ->
      begin match v with
      | Any VTuple (v1, v2) ->
        let* w1 = wrap v1 t1 in
        let* w2 = wrap v2 t2 in
        if w1 == v1 && w2 == v2 then
          return v (* return value unchanged because wrapping did nothing *)
        else
          return_any (VTuple (w1, w2))
      | _ -> mismatch @@ wrap_non_tuple v t
      end
    | VTypeRefine { var = _ ; tau ; predicate = _ } ->
      wrap v tau

  (*
    Wrap with FIFO queue of types, represented as a list.
    That is, the last type in the list wraps first.
  *)
  and wrap_multi
    : 'env. Val.tval list -> Val.any -> (Val.any, 'env) m
    = fun queue v ->
    List.fold_right (fun twrap acc_m ->
      let* acc = acc_m in
      wrap acc twrap
    ) queue (return v)

  (*
    ---------------------------------------
    EVALUATE LIST OF STATEMENTS TO A MODULE
    ---------------------------------------

    Uses the environment when evaluating.
  *)
  and eval_statement_list (statements : Ast.statement list) : (Val.any, Val.Env.t) m =
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

    Uses the environment when evaluating.
  *)
  and eval_statement (stmt : Ast.statement) : (Ident.t * Val.any, Val.Env.t) m =
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
        let* self =
          if do_splay then
            gen tval
          else
            wrap (Any (
              VFunFix { fvar = item ; param ; closure = { captured = defn ; env } }
            )) tval
        in
        (* we don't just return a wrapped fix fun because that would skip the check *)
        return_any (VFunClosure { param ; closure =
          { captured = defn ; env = Env.set item self env } }
        )
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

    Uses the environment when evaluating.
  *)
  and force_eval (expr : Ast.t) : (Val.any, Val.Env.t) m =
    let* v = eval expr in
    force_value v
  
  (*
    --------------------
    FORCE VALUES TO WHNF
    --------------------

    Does not use the environment.
  *)
  and force_value 
    : 'env. Val.any -> (Val.any, 'env) m
    = fun v ->
    if do_splay then
      match v with 
      | Any VLazy vlazy -> resolve_lazy vlazy
      | _ -> return v
    else
      (* without splaying, nothing is ever delayed because it would be incomplete *)
      return v

  (*
    Forces the value to weak head normal form and wraps
    with any lazily-done wrappings.

    Since this changes the order of when inputs happen, this
    messes up the checking of deterministic functions.
      TODO: fix this.
  *)
  and resolve_lazy
    : 'env. Val.lazy_cell -> (Val.any, 'env) m
    = fun { cell ; wrapping_types } ->
    assert do_splay;
    let* v_any =
      let lazy_v = State.get_cell cell in
      match lazy_v with
      | LLazy lv ->
        let* genned =
          match lv with
          | LGenMu { var ; closure } -> force_gen_mu var closure
          | LGenList t -> force_gen_list t
        in
        State.set_cell cell (LValue genned);
        return genned
      | LValue v_any ->
        return v_any
    in
    wrap_multi wrapping_types v_any

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
