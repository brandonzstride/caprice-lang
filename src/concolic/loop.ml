
open Common

let max_tree_depth = 30
let max_step = Interp.Step.Step 100_000

let make_targets (target : Target.t) (path : Path.t) (ienv : Ienv.t) 
  ~(max_tree_depth : int) : Target.t list * bool =
  let n = Target.path_length target in
  let stem = Path.drop_prefix n path in
  let pruned = ref false in
  let (new_targets, _, _) = 
    List.fold_left (fun ((acc_set, len, formulas) as acc) pathunit ->
      if len > max_tree_depth then (pruned := true; acc) else
      let size = len + 1 in
      match pathunit with
      | Path.Nonflipping formula ->
        acc_set, size, Formula.BSet.add formula formulas
      | Formula (formula, key) ->
        let new_ienv = Ienv.remove_greater key ienv in
        let new_target =
          Target.make (Formula.not_ formula) formulas new_ienv 
            ~size
        in
        new_target :: acc_set, size, Formula.BSet.add formula formulas
      | Label { key ; label = { main = _ ; alts } } ->
        let new_ienv = Ienv.remove_greater key ienv in
        List.fold_left (fun acc alt_label ->
          Target.make 
            (Formula.const_bool true)
            formulas
            (Ienv.add (KLabel key) alt_label new_ienv)
            ~size
          :: acc
        ) acc_set alts
        , size, formulas
    ) ([], n, target.all_formulas) stem
  in
  new_targets, !pruned

let loop (solve : Stepkey.t Smt.Formula.solver) (expr : Lang.Ast.t) (tq : Target_queue.t) =
  let rec loop tq =
    match Target_queue.pop tq with
    | Some (target, tq) ->
      begin match solve target.target_formula with
      | Sat model -> loop_on_model target tq model
      | Unknown -> let a = loop tq in Answer.min Answer.Unknown a
      | Unsat -> loop tq
      end
    | None -> Answer.Exhausted

  and loop_on_model target tq model =
    let ienv = Ienv.extend target.i_env (Ienv.of_model model) in
    let res, state = Eval.eval expr ienv ~max_step in
    let k ~reached_max_step =
      let targets, is_pruned = make_targets target state.path state.logged_inputs ~max_tree_depth in
      let a = loop (Target_queue.push_list tq targets) in
      if is_pruned || reached_max_step
      then Answer.min Answer.Exhausted_pruned a
      else a
    in
    match res with
    | (Refutation _ | Mismatch _ | Assert_false | Unbound_variable _) -> Error
    | Done | Vanish | Confirmation -> k ~reached_max_step:false
    | Reach_max_step _ -> k ~reached_max_step:true
  in
  loop tq


