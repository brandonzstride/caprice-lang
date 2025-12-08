
open Lang
open Common
open Effects
open Cvalue

(* `Any` is unboxed, so this is zero overhead *)
let[@inline always] return_any v = return (Any v)

[@@@warning "-27"]
[@@@warning "-26"]

let eval
  (expr : Ast.t)
  (input_env : Ienv.t)
  ~(max_step : Interp.Step.t)
  : Err.t * Path.t
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
        Features.Record.fold (fun l e acc_m ->
          let* acc = acc_m in
          let* v = eval e in
          return (Labels.Record.Map.add l v acc)
        ) (return Features.Record.empty) e_record_body
      in
      return_any (VRecord record_body)
    | ELet { var ; defn ; body } ->
      let* v = eval defn in
      local (Env.set var v) (eval body)
    | EAppl { func ; arg } ->
      let* v_func = eval func in
      begin match v_func with
      | Any VFunClosure { param ; closure = { body ; env } } ->
        let* v_arg = eval arg in
        local (fun _ -> Env.set param v_arg env) (eval body)
      | Any VGenFun { domain ; codomain } ->
        let* v_arg = eval arg in
        let* step = step in
        let* input = read_and_log_input (KLabel (Stepkey step)) input_env Eval in
        begin match input with
        | Check ->
          let* () = push_label { key = Stepkey step ; label = Interp.Label.With_alt.check } in
          check v_arg domain
        | Eval ->
          let* () = push_label { key = Stepkey step ; label = Interp.Label.With_alt.eval } in
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
          | Match_bindings e ->
            local (fun env -> Env.extend env e) (eval body)
          | No_match -> find_match tl
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
    (* symbolic values and branching *)
    | EPick_i -> failwith "Unimplemented; TODO"
    | ENot e ->
      let* v = eval e in
      begin match v with
      | Any VBool (b, s) -> return_any (VBool (not b, Smt.Formula.not_ s))
      | _ -> fail (Mismatch "Non-bool `not`.")
      end
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
    | ELetTyped { var = { var ; tau } ; defn ; body } ->
      let* tval = eval_type tau in
      let* v = eval defn in
      let* step = step in
      let* input = read_and_log_input (KLabel (Stepkey step)) input_env Check in
      begin match input with
      | Check ->
        let* () = push_label { key = Stepkey step ; label = Interp.Label.With_alt.check } in
        check v tval
      | Eval ->
        let* () = push_label { key = Stepkey step ; label = Interp.Label.With_alt.eval } in
        (* TODO: wrap *)
        local (Env.set var v) (eval defn)
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
        Features.Record.fold (fun l e acc_m ->
          let* acc = acc_m in
          let* tval = eval_type e in
          return (Labels.Record.Map.add l tval acc)
        ) (return Features.Record.empty) t_record_body
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
    | ETypeVariant ls ->
      let* variant_bodies =
        List.fold_left (fun acc_m { Features.Variant.label ; payload } ->
          let* acc = acc_m in
          let* tval = eval_type payload in
          return (Labels.Variant.Map.add label tval acc)
        ) (return Labels.Variant.Map.empty) ls
      in
      return_any (VTypeVariant variant_bodies)
    | _ -> failwith ""

  and eval_type (expr : Ast.t) : Cvalue.tval m =
    let* v = eval expr in
    handle_any v
      ~data:(fun _ -> fail (Mismatch "Data value in type"))
      ~typeval:return

  and check (v : Cvalue.any) (t : Cvalue.tval) : Cvalue.any m =
    let* () = incr_step ~max_step in
    failwith ""

  and gen (t : Cvalue.tval) : Cvalue.any m =
    let* () = incr_step ~max_step in
    match t with
    | VTypeUnit -> return_any VUnit
    | VTypeInt ->
      let* step = step in
      let* i = read_and_log_input (KInt (Stepkey step)) input_env 0 in
      return_any (VInt (i, Stepkey.int_symbol step))
    | VTypeBool ->
      let* step = step in
      let* b = read_and_log_input (KBool (Stepkey step)) input_env false in
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
        Features.Record.fold (fun l t acc_m ->
          let* acc = acc_m in
          let* v = gen t in
          return (Labels.Record.Map.add l v acc)
        ) (return Features.Record.empty) record_t
      in
      return_any (VRecord genned_body)
    | VTypeVariant variant_t ->
      let* step = step in
      let* l =
        read_and_log_input (KLabel (Stepkey step)) input_env
          (* TODO: choose nonrecursive variant constructor by default instead of an arbitrary one *)
          (Interp.Label.of_variant_label (fst @@ Labels.Variant.Map.choose variant_t))
      in
      begin match l with
      | Label id ->
        begin match Labels.Variant.Map.find_opt (VariantLabel id) variant_t with
        | Some t ->
          let* () = 
            push_label { key = Stepkey step ; label = { main = Label id ; alts =
              Labels.Variant.Map.remove (VariantLabel id) variant_t
              |> Labels.Variant.Map.to_list
              |> List.map (fun (Labels.Variant.VariantLabel l_id, _) -> Interp.Label.Label l_id) } }
          in
          let* v = gen t in
          return_any (VVariant { label = VariantLabel id ; payload = v })
        | None -> fail (Mismatch "Missing variant label to generate")
        end
      | _ -> fail (Mismatch "Bad input env")
      end
    | VTypeRefine { var ; tau ; predicate = { body ; env } } ->
      let* v = gen tau in
      let* p = local (fun _ -> Env.set var v env) (eval body) in
      begin match p with
      | Any VBool (b, s) ->
        if b then 
          let* () = push_formula ~allow_flip:false s in
          return v
        else 
          let* () = push_formula (Smt.Formula.not_ s) in
          fail Vanish
      | _ -> fail (Mismatch "Non-bool predicate")
      end 
    | VTypeMu { var ; closure = { body ; env } } as v ->
      let* t = local (fun _ -> Env.set var (Any v) env) (eval_type body) in
      gen t
  in

  run (eval expr)
