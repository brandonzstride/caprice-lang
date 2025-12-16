
open Common

let max_tree_depth = 30
let max_step = Interp.Step.Step 100_000

let make_targets (target : Target.t) (stem : Path.t) (ienv : Ienv.t) 
  ~(max_tree_depth : int) : Target.t list * bool =
  Utils.List_utils.fold_left_until (fun (acc_set, len, formulas) pathunit ->
    if len > max_tree_depth then 
      `Stop (acc_set, true)
    else
      let size = len + 1 in
      match pathunit with
      | Path.Nonflipping formula ->
        `Continue (acc_set, size, Formula.BSet.add formula formulas)
      | Formula (formula, key) ->
        let new_ienv = Ienv.remove_greater key ienv in
        let new_target =
          Target.make (Formula.not_ formula) formulas new_ienv 
            ~size
        in
        `Continue (new_target :: acc_set, size, Formula.BSet.add formula formulas)
      | Label { key ; label = { main = _ ; alts } } ->
        let new_ienv = Ienv.remove_greater key ienv in
        `Continue (
          List.fold_left (fun acc alt_label ->
            Target.make 
              Formula.trivial
              formulas
              (Ienv.add (KLabel key) alt_label new_ienv)
              ~size
            :: acc
          ) acc_set alts
          , size, formulas
        )
  ) (fun (acc_set, _, _) -> acc_set, false)
  ([], Target.path_length target, target.all_formulas) stem

let targets_of_logged_runs (runs : Effects.Logged_run.t list) ~(max_tree_depth : int) : Target.t list * bool =
  List.fold_left (fun (targets, is_pruned) run ->
    let new_targets, new_is_pruned = 
      let open Effects.Logged_run in
      make_targets run.target (List.rev run.rev_stem) run.inputs ~max_tree_depth
    in
    new_targets @ targets, is_pruned || new_is_pruned
  ) ([], false) runs

let c = Utils.Counter.create ()

module T = Smt.Formula.Make_transformer (Overlays.Typed_z3)

let loop (solve : Stepkey.t Smt.Formula.solver) (pgm : Lang.Ast.program) (tq : Target_queue.t) =
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
    let _ = Utils.Counter.next c in
    let ienv = Ienv.extend target.i_env (Ienv.of_model model) in
    let res, runs = Eval.eval pgm ienv target ~max_step in
    if Eval_result.is_signal_to_stop res
    then Eval_result.to_answer res
    else 
      Answer.min (Eval_result.to_answer res) @@ 
        let targets, is_pruned = 
          targets_of_logged_runs runs ~max_tree_depth
        in
        let a = loop (Target_queue.push_list tq targets) in
        if is_pruned
        then Answer.min Answer.Exhausted_pruned a
        else a
  in
  loop tq

module Default_Z3 = Overlays.Typed_z3.Default
module Default_solver = Smt.Formula.Make_solver (Default_Z3)

let begin_ceval (pgm : Lang.Ast.program) : Answer.t =
  let span, answer = Utils.Time.time (loop Default_solver.solve pgm) Target_queue.initial in
  Format.printf "Finished type checking in %0.3f ms and %d runs:\n    %s\n"
    (Utils.Time.span_to_ms span) !(c.cell) (Answer.to_string answer);
  answer