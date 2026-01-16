
open Grammar

let make_targets ~(max_tree_depth : int) (target : Target.t)
  (stem : Path.t) : Target.t list * bool =
  Utils.List_utils.fold_left_until (fun (acc_set, len, formulas) p_item ->
    if Path_priority.to_int len > max_tree_depth then
      `Stop (acc_set, true)
    else
      let path_priority = Path_priority.plus_int len (Path_item.to_priority p_item) in
      match p_item with
      | Path_item.Nonflipping formula ->
        `Continue (acc_set, path_priority, Formula.BSet.add formula formulas)
      | Formula { cond ; logged_inputs } ->
        let new_target =
          Target.make (Formula.not_ cond) formulas logged_inputs
            ~path_priority
        in
        `Continue (new_target :: acc_set, path_priority, Formula.BSet.add cond formulas)
      | Tag { tag = _ ; alternatives ; key ; logged_inputs } ->
        `Continue (
          List.fold_left (fun acc alt_tag ->
            Target.make 
              Formula.trivial
              formulas
              (Input_env.add KTag key alt_tag logged_inputs)
              ~path_priority:(Path_priority.plus_int len (Tag.priority alt_tag))
            :: acc
          ) acc_set alternatives
          , path_priority, formulas
        )
  ) (fun (acc_set, _, _) -> acc_set, false)
  ([], Target.priority target, target.all_formulas) stem

let collect_logged_runs ~(max_tree_depth : int) (runs : Logged_run.t list) : Target.t list * bool * Answer.t =
  List.fold_left (fun (targets, is_pruned, answer) run ->
    let new_targets, new_is_pruned = 
      let open Logged_run in
      make_targets run.target (Rev_stem.to_forward_path run.rev_stem) ~max_tree_depth
    in
    new_targets @ targets, is_pruned || new_is_pruned, Answer.min answer run.answer
  ) ([], false, Exhausted) runs

let c = Utils.Counter.create ()

let make_int_feeder ~(run_num : int) : unit -> int =
  if run_num = 1 then
    fun () -> 0
  else
    fun () -> Random.int_in_range ~min:(-10) ~max:10

let make_bool_feeder ~(run_num : int) : unit -> bool =
  if run_num = 1 then
    fun () -> false
  else
    Random.bool

open Lwt.Let_syntax.Let_syntax
open Lwt.Syntax

(* Does not do its own timeout, even though timeout is passed in with options *)
let loop ~(options : Options.t) (solve : Stepkey.t Smt.Formula.solver) 
  (pgm : Lang.Ast.program) (tq : Target_queue.t) : Answer.t Lwt.t =
  let eval =
    Eval.eval pgm ~max_step:options.max_step ~do_splay:options.do_splay
      ~do_wrap:options.do_wrap
  in
  let rec loop tq =
    let* () = Lwt.pause () in
    match Target_queue.pop tq with
    | Some (target, tq) ->
      begin match solve target.target_formula with
      | Sat model -> loop_on_model target tq model
      | Unknown -> 
        let* a = loop tq in
        return @@ Answer.min Answer.Unknown a
      | Unsat -> loop tq
      end
    | None -> return Answer.Exhausted

  and loop_on_model target tq model =
    let run_num = Utils.Counter.next c in
    let ienv = Input_env.extend target.i_env (Input_env.of_model model) in
    let answer, runs =
      eval ienv target
        ~default_int:(make_int_feeder ~run_num)
        ~default_bool:(make_bool_feeder ~run_num)
    in
    if Answer.is_signal_to_stop answer
    then return answer
    else
      let* loop_answer =
        let targets, is_pruned, forked_answer = 
          collect_logged_runs runs ~max_tree_depth:options.max_tree_depth
        in
        let* a = loop (Target_queue.push_list tq targets) in
        return @@
        Answer.min forked_answer @@
          if is_pruned
          then Answer.min Answer.Exhausted_pruned a
          else a
      in
      return @@ Answer.min answer loop_answer
  in
  loop tq

module Default_Z3 = Overlays.Typed_z3.Default
module Default_solver = Smt.Formula.Make_solver (Default_Z3)

let begin_ceval ?(print_outcome : bool = true) ~(options : Options.t)
  (pgm : Lang.Ast.program) : Answer.t =
  let go () =
    try
      let time_sec = Utils.Time.convert_span options.global_timeout ~to_:Mtime.Span.s in
      Lwt_main.run (Lwt_unix.with_timeout time_sec @@ fun () ->
        loop Default_solver.solve pgm Target_queue.initial ~options
      )
    with
    | Lwt_unix.Timeout -> Answer.Timeout options.global_timeout
  in
  Utils.Counter.reset c;
  if options.is_random then Random.self_init () else Random.init 999;
  let span, answer = Utils.Time.time go () in
  if print_outcome then
  Format.printf "Finished type checking in %0.3f ms and %d runs:\n    %s\n"
    (Utils.Time.span_to_ms span) !(c.cell) (Answer.to_string answer);
  answer