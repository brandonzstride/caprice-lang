
open Lang
open Interp
open Common

(* Logs from other runs that are not the main run *)
module Logged_run = struct
  type t =
    { rev_stem : Path.t
    ; inputs : Ienv.t
    ; target : Target.t } 
end

module State = struct
  type t = 
    { rev_stem : Path.t (* we will cons to the path instead of union a log *)
    ; logged_inputs : Ienv.t 
    ; branch_depth : int (* only the branch depth while not yet at the target *)
    ; runs : Logged_run.t Utils.Diff_list.t
    }

  let empty : t =
    { rev_stem = Path.empty
    ; logged_inputs = Ienv.empty
    ; branch_depth = 0 
    ; runs = Utils.Diff_list.empty }
end

module Context = struct
  type t =
    { target : Target.t } 
end

include Effects.Make (State) (Cvalue.Env) (Context) (Eval_result)

let vanish : 'a m =
  fail Vanish

(* We will also want to log this label in input env, but at what time? *)
let push_label (label : Label.With_alt.t) : unit m =
  let* step = step in
  let* { target } = read_ctx in
  modify (fun s -> 
    if s.branch_depth >= Target.path_length target
    then 
      { s with rev_stem = Path.cons_label { key = Stepkey step ; label } s.rev_stem 
      ; branch_depth = s.branch_depth + 1 }
    else 
      { s with branch_depth = s.branch_depth + 1 }
  )

(* Pushes the label to the path and logs it in input environment *)
let push_and_log_label (label : Label.t) : unit m =
  let* step = step in
  let* { target } = read_ctx in
  modify (fun s -> 
    { s with
      branch_depth = s.branch_depth + 1
    ; logged_inputs = Ienv.add (KLabel (Stepkey step)) label s.logged_inputs
    ; rev_stem = 
      if s.branch_depth >= Target.path_length target
      then Path.cons_label { key = Stepkey step ; label = { main = label ; alts = [] } } s.rev_stem 
      else s.rev_stem
    }
  )

let push_formula ?(allow_flip : bool = true) (formula : (bool, Stepkey.t) Smt.Formula.t) : unit m =
  if Smt.Formula.is_const formula
  then return ()
  else
    let* step = step in
    let* { target } = read_ctx in
    modify (fun s -> 
      if s.branch_depth >= Target.path_length target
      then 
        { s with rev_stem =
          if allow_flip
          then Path.cons_formula formula (Stepkey step) s.rev_stem
          else Path.cons_nonflipping formula s.rev_stem
        ; branch_depth = s.branch_depth + 1 }
      else
        { s with branch_depth = s.branch_depth + 1 }
    )

let log_input (key : 'a Ienv.Key.t) (input : 'a) : unit m =
  modify (fun s -> { s with logged_inputs = Ienv.add key input s.logged_inputs })

let read_input (make_key : Stepkey.t -> 'a Ienv.Key.t) (input_env : Ienv.t) : 'a option m =
  let* step = step in
  let key = make_key (Stepkey step) in
  return (Ienv.find key input_env)

let read_and_log_input_with_default (make_key : Stepkey.t -> 'a Ienv.Key.t) 
  (input_env : Ienv.t) ~(default : 'a) : 'a m =
  let* step = step in
  let key = make_key (Stepkey step) in
  match Ienv.find key input_env with
  | Some i -> let* () = log_input key i in return i
  | None -> let* () = log_input key default in return default

let target_to_here : Target.t m =
  let* { target } = read_ctx in
  let* state = get in
  if state.branch_depth < Target.path_length target
  then fail (Mismatch "Have not surpassed target")
  else
    return @@
    Target.make Formula.trivial
      (Formula.BSet.union target.all_formulas (Path.formulas state.rev_stem))
      state.logged_inputs
      ~size:(Target.path_length target + List.length state.rev_stem)

let fork (forked_m : Eval_result.t u) : unit m =
  let* target = target_to_here in
  fork forked_m { target }
    ~setup_state:(fun state ->
      { state with rev_stem = Path.empty }
    )
    ~restore_state:(fun ~og ~forked_state ->
      { og with runs =
        let forked_run =
          { Logged_run.rev_stem = forked_state.rev_stem ; inputs = forked_state.logged_inputs ; target }
        in
        let open Utils.Diff_list in
        (* Note that the forked state runs include the original runs (because it inhereted state)! *)
        forked_run -:: forked_state.runs (* ... hence, don't copy the og runs *)
      }
    )
    (fun res ->
      if Eval_result.is_signal_to_stop res (* FIXME: need to mark as pruned *)
      then fail res (* propagate up the failure *)
      else return ())

let run' (x : 'a m) (target : Target.t) (s : State.t) (e : Cvalue.Env.t) : Eval_result.t * State.t =
  match run x s e { target } with
  | Ok _, state, _ -> Done, state
  | Error e, state, _ -> e, state

let run (x : 'a m) (target : Target.t) : Eval_result.t * State.t =
  run' x target State.empty Env.empty
