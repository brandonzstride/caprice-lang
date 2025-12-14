
open Lang
open Common
open Effects
open Cvalue

(* `Any` is unboxed, so this is zero overhead *)
let[@inline always] return_any v = return (Any v)

open Ienv.Key

let eval
  (expr : Ast.t)
  (input_env : Ienv.t)
  (target : Target.t)
  ~(max_step : Interp.Step.t)
  : Eval_result.t * State.t
  =
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
      return_any (VFunClosure { param ; closure = { body ; env }})
    | ERecord e_record_body -> 
      let* record_body =
        Record.fold (fun l e acc_m ->
          let* acc = acc_m in
          let* v = eval e in
          return (Labels.Record.Map.add l v acc)
        ) (return Record.empty) e_record_body
      in
      return_any (VRecord record_body)
    | ELet { var = VarUntyped { name } ; defn ; body } ->
      let* v = eval defn in
      local (Env.set name v) (eval body)
    | ELetRec { var = VarUntyped { name } ; param ; defn ; body } ->
      let* env = read in
      let v = to_any (VFunFix { fvar = name ; param ; closure = { body = defn ; env } }) in
      local (Env.set name v) (eval body)
    | EAppl { func ; arg } ->
      let* v_func = eval func in
      begin match v_func with
      | Any VFunClosure { param ; closure = { body ; env } } ->
        let* v_arg = eval arg in
        local (fun _ -> Env.set param v_arg env) (eval body)
      | (Any VFunFix { fvar ; param ; closure = { body ; env } }) as vfun ->
        let* v_arg = eval arg in
        local (fun _ -> 
          Env.set fvar vfun env
          |> Env.set param v_arg
        ) (eval body)
      | Any VGenFun { domain ; codomain } ->
        let* v_arg = eval arg in
        let* input = read_and_log_input make_label input_env Eval in
        begin match input with
        | Check ->
          let* () = push_label Interp.Label.With_alt.check in
          check v_arg domain
        | Eval ->
          let* () = push_label Interp.Label.With_alt.eval in
          gen codomain
        | _ -> fail (Mismatch "Bad input env")
        end
      | _ -> fail (Mismatch "Apply non-function.")
      end
    | EMatch { subject ; patterns } ->
      let* v = eval subject in
      let rec find_match = function
        | [] -> fail (Mismatch "Missing pattern.")
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
      let* v = eval record in
      begin match v with
      | Any VRecord record_body ->
        begin match Labels.Record.Map.find_opt label record_body with
        | Some v' -> return v'
        | None -> fail (Mismatch "Missing label.")
        end
      | _ -> fail (Mismatch "Project non-record.")
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
      let* v2 = eval e2 in
      begin match v2 with
      | Any (VEmptyList as tl)
      | Any (VListCons _ as tl) -> return_any (VListCons (v1, tl))
      | _ -> fail (Mismatch "Cons non-list.")
      end
    (* symbolic values and branching *)
    | EPick_i ->
      let* step = step in
      let* i = read_and_log_input make_int input_env 0 in
      return_any (VInt (i, Stepkey.int_symbol step))
    | ENot e ->
      let* v = eval e in
      begin match v with
      | Any VBool (b, s) -> return_any (VBool (not b, Smt.Formula.not_ s))
      | _ -> fail (Mismatch "Non-bool `not`.")
      end
    | EBinop { left ; binop ; right } ->
      let* vleft = eval left in
      let* vright = eval right in
      let fail_binop = fail (Mismatch "Bad binop") in
      let value_binop a b =
        let k f s1 s2 op =
          return_any @@ f (Smt.Formula.binop op s1 s2)
        in
        let v_int n s = VInt (n, s) in
        let v_bool n s = VBool (n, s) in
        match binop, a, b with
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
        | BOr          , VBool (b1, e1) , VBool (b2, e2)             -> k (v_bool (b1 || b2)) e1 e2 Or
        | BAnd         , VBool (b1, e1) , VBool (b2, e2) -> return_any @@ VBool (b1 && b2, Smt.Formula.and_ [ e1 ; e2 ])
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
              match binop with
              | BTimes -> return_any (VTypeTuple (type_left, type_right))
              | _ -> fail_binop
            )
        )
    | EIf { if_ ; then_ ; else_ } ->
      let* v = eval if_ in
      begin match v with
      | Any VBool (b, s) ->
        let cont = if b then then_ else else_ in
        let* () = push_formula (if b then s else Smt.Formula.not_ s) in
        eval cont 
      | _ -> fail (Mismatch "Non-bool `if`.")
      end
    | EAssert e ->
      let* v = eval e in
      begin match v with
      | Any VBool (b, s) ->
        if b then
          let* () = push_formula s in
          return_any VUnit
        else
          let* () = push_formula (Smt.Formula.not_ s) in
          fail Assert_false
      | _ -> fail (Mismatch "Non-bool `assert`.")
      end
    | EAssume e ->
      let* v = eval e in
      begin match v with
      | Any VBool (b, s) ->
        if b then
          let* () = push_formula ~allow_flip:false s in
          return_any VUnit
        else
          let* () = push_formula (Smt.Formula.not_ s) in
          fail Vanish
      | _ -> fail (Mismatch "Non-bool `assume`.")
      end
    | ELet { var = VarTyped { name ; tau } ; defn ; body } ->
      let* tval = eval_type tau in
      let* v = eval defn in
      let* input = read_and_log_input make_label input_env Check in
      begin match input with
      | Check ->
        let* () = push_label Interp.Label.With_alt.check in
        check v tval
      | Eval ->
        let* () = push_label Interp.Label.With_alt.eval in
        (* TODO: wrap *)
        local (Env.set name v) (eval body)
      | _ -> fail (Mismatch "Bad input env")
      end
    | ELetRec { var = VarTyped { name ; tau } ; param ; defn ; body } ->
      let* tval = eval_type tau in
      let* env = read in
      let v = to_any (VFunFix { fvar = name ; param ; closure = { body = defn ; env } }) in
      let* input = read_and_log_input make_label input_env Check in
      begin match input with
      | Check ->
        let* () = push_label Interp.Label.With_alt.check in
        check v tval
      | Eval ->
        let* () = push_label Interp.Label.With_alt.eval in
        (* TODO: wrap *)
        local (Env.set name v) (eval body)
      | _ -> fail (Mismatch "Bad input env")
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
    | ETypeFun { domain ; codomain } ->
      let* dom_t = eval_type domain in
      let* cod_t = eval_type codomain in
      return_any (VTypeFun { domain = dom_t ; codomain = cod_t })
    | ETypeRefine { var ; tau ; predicate } ->
      let* tval = eval_type tau in
      let* env = read in
      return_any (VTypeRefine { var ; tau = tval ; predicate = { body = predicate ; env }})
    | ETypeMu { var ; body } ->
      let* env = read in
      return_any (VTypeMu { var ; closure = { body ; env } })
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

  and eval_type (expr : Ast.t) : Cvalue.tval m =
    let* v = eval expr in
    handle_any v
      ~data:(fun _ -> fail (Mismatch "Data value in type"))
      ~typeval:return

  and check : 'a. Cvalue.any -> Cvalue.tval -> 'a m = fun v t ->
    let refute = fail (Refutation (v, t)) in
    let confirm = fail Confirmation in
    let* () = incr_step ~max_step in
    match t with
    | VTypeInt ->
      begin match v with
      | Any VInt _ -> confirm
      | _ -> refute
      end
    | VTypeBool ->
      begin match v with
      | Any VBool _ -> confirm
      | _ -> refute
      end
    | VTypeUnit ->
      begin match v with
      | Any VUnit -> confirm
      | _ -> refute
      end
    | VTypeTop -> failwith "Unimplemented check top"
    | VTypeBottom -> refute
    | VTypePoly { id } ->
      begin match v with
      | Any VGenPoly { id = id' ; nonce = _ } when id = id' -> confirm
      | _ -> refute
      end
    | VType ->
      (* TODO: consider a wellformedness check *)
      handle_any v ~data:(fun _ -> refute) ~typeval:(fun _ -> confirm)
    | VTypeFun { domain ; codomain } ->
      begin match v with
      | Any VFunClosure { param ; closure = { body ; env } } ->
        let* genned = gen domain in
        let* res = local (fun _ -> Env.set param genned env) (eval body) in
        check res codomain
      | (Any VFunFix { fvar ; param ; closure = { body ; env } }) as vfun ->
        let* genned = gen domain in
        let* res = local (fun _ -> 
            Env.set fvar vfun env
            |> Env.set param genned
          ) (eval body)
        in
        check res codomain 
      | Any VGenFun { domain = domain' ; codomain = codomain' } ->
        let* l = read_and_log_input make_label input_env Left in
        begin match l with
        | Left ->
          let* () = push_label Interp.Label.With_alt.left in
          if domain == domain' || domain = domain' then confirm else
          let* genned = gen domain in
          check genned domain'
        | Right ->
          let* () = push_label Interp.Label.With_alt.right in
          if codomain == codomain' || codomain = codomain' then confirm else
          let* genned = gen codomain' in
          check genned codomain
        | _ -> fail (Mismatch "Bad input env")
        end
      | _ -> refute
      end
    | VTypeVariant variant_t ->
      begin match v with
      | Any VVariant { label ; payload } ->
        begin match Labels.Variant.Map.find_opt label variant_t with
        | Some t -> check payload t
        | None -> refute
        end
      | _ -> refute
      end
    | VTypeRecord record_t ->
      begin match v with
      | Any VRecord record_v ->
        let t_labels = Record.label_set record_t in
        let v_labels = Record.label_set record_v in
        if Labels.Record.Set.subset t_labels v_labels
        then
          let* l =
            read_and_log_input make_label input_env
              (Interp.Label.of_record_label (Labels.Record.Set.choose t_labels))
          in
          begin match l with
          | Label id ->
            let to_check = Labels.Record.of_ident id in
            let t = Labels.Record.Map.find to_check record_t in
            let v = Labels.Record.Map.find to_check record_v in
            let* () =
              push_label Interp.Label.With_alt.{ main = l ; alts =
                Labels.Record.Set.remove to_check t_labels
                |> Labels.Record.Set.to_list
                |> List.map Interp.Label.of_record_label
              }
            in
            check v t
          | _ -> fail (Mismatch "Bad input env")
          end
        else refute
      | _ -> refute
      end
    | VTypeMu { var ; closure = { body ; env } } ->
      let* t_body = local (fun _ -> Env.set var (Any t) env) (eval_type body) in
      check v t_body
    | VTypeList t ->
      begin match v with
      | Any VEmptyList -> confirm
      | Any VListCons (v_hd, v_tl) ->
        let* l = read_and_log_input make_label input_env Left in
        begin match l with
        | Left ->
          let* () = push_label Interp.Label.With_alt.left in
          check v_hd t
        | Right ->
          let* () = push_label Interp.Label.With_alt.right in
          check (Any v_tl) (VTypeList t)
        | _ -> fail (Mismatch "Bad input env")
        end
      | _ -> refute
      end
    | VTypeRefine { var ; tau ; predicate = { body ; env } } ->
      let* l = read_and_log_input make_label input_env Check in
      begin match l with
      | Check -> 
        let* () = push_label Interp.Label.With_alt.check in
        check v tau
      | Eval -> 
        let* () = push_label Interp.Label.With_alt.eval in
        let* p = local (fun _ -> Env.set var v env) (eval body) in
        begin match p with
        | Any VBool (b, s) ->
          if b then 
            let* () = push_formula s in
            confirm
          else 
            let* () = push_formula ~allow_flip:false (Smt.Formula.not_ s) in
            refute
        | _ -> fail (Mismatch "Non-bool predicate")
        end 
      | _ -> fail (Mismatch "Bad input env")
      end
    | VTypeTuple (t1, t2) ->
      begin match v with
      | Any VTuple (v1, v2) ->
        let* l = read_and_log_input make_label input_env Left in
        begin match l with
        | Left ->
            let* () = push_label Interp.Label.With_alt.left in
            check v1 t1
        | Right ->
            let* () = push_label Interp.Label.With_alt.right in
            check v2 t2
        | _ -> fail (Mismatch "Bad input env")
        end
      | _ -> refute
      end

  and gen (t : Cvalue.tval) : Cvalue.any m =
    let* () = incr_step ~max_step in
    match t with
    | VTypeUnit -> return_any VUnit
    | VTypeInt ->
      let* step = step in
      let* i = read_and_log_input make_int input_env 0 in
      return_any (VInt (i, Stepkey.int_symbol step))
    | VTypeBool ->
      let* step = step in
      let* b = read_and_log_input make_bool input_env false in
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
        read_and_log_input make_label input_env
          (* TODO: choose a nonrecursive variant constructor instead of an arbitrary one *)
          (Interp.Label.of_variant_label (Labels.Variant.Set.choose t_labels))
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
      | _ -> fail (Mismatch "Bad input env")
      end
    | VTypeList t ->
      let* l = read_and_log_input make_label input_env Left in
      begin match l with
      | Left ->
        let* () = push_label Interp.Label.With_alt.left in
        return_any VEmptyList
      | Right ->
        let* () = push_label Interp.Label.With_alt.right in
        let* hd = gen t in
        let* Any tl = gen (VTypeList t) in
        return_any (VListCons (hd, Obj.magic tl)) (* MAGIC: Safe because always returns data *)
      | _ -> fail (Mismatch "Bad input env")
      end
    | VTypeRefine { var ; tau ; predicate = { body ; env } } ->
      let* v = gen tau in
      let* p = local (fun _ -> Env.set var v env) (eval body) in
      begin match p with
      | Any VBool (true, s) ->
        let* () = push_formula ~allow_flip:false s in
        return v
      | Any VBool (false, s) ->
        let* () = push_formula (Smt.Formula.not_ s) in
        fail Vanish
      | _ -> fail (Mismatch "Non-bool predicate")
      end 
    | VTypeMu { var ; closure = { body ; env } } ->
      let* t_body = local (fun _ -> Env.set var (Any t) env) (eval_type body) in
      gen t_body
    | VTypeTuple (t1, t2) ->
      let* v1 = gen t1 in
      let* v2 = gen t2 in
      return_any (VTuple (v1, v2))
  in

  run (eval expr) target
