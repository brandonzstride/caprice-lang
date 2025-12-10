
open Lang
open Interp
open Common

module State = struct
  type t = 
    { rev_path : Path.t (* we will cons to the path instead of union a log *)
    ; logged_inputs : Ienv.t }

  let empty : t =
    { rev_path = Path.empty
    ; logged_inputs = Ienv.empty }
end

module Err = struct
  type t = 
    | Refutation of Cvalue.any * Cvalue.tval
    | Confirmation
    | Mismatch of string
    | Assert_false
    | Vanish
    | Unbound_variable of Ident.t
    | Reach_max_step of Step.t
    | Done
    (* [@@deriving eq] *)

  let fail_on_fetch (i : Ident.t) (s : State.t) : t * State.t =
    Unbound_variable i, s

  let fail_on_max_step (n : Step.t) (s : State.t) : t * State.t =
    Reach_max_step n, s
end

include Effects.Make (State) (Cvalue.Env) (Err)

let vanish : 'a m =
  fail Vanish

let push_label (label : Label.With_alt.t) : unit m =
  let* step = step in
  modify (fun s -> { s with rev_path = Path.cons_label { key = Stepkey step ; label } s.rev_path })

let push_formula ?(allow_flip : bool = true) (formula : (bool, Stepkey.t) Smt.Formula.t) : unit m =
  if Smt.Formula.is_const formula
  then return ()
  else 
    if allow_flip
    then
      let* step = step in
      modify (fun s -> { s with rev_path = Path.cons_formula formula (Stepkey step) s.rev_path })
    else
      modify (fun s -> { s with rev_path = Path.cons_nonflipping formula s.rev_path })

let log_input (key : 'a Ienv.Key.t) (input : 'a) : unit m =
  modify (fun s -> { s with logged_inputs = Ienv.add key input s.logged_inputs })

let read_and_log_input (make_key : Stepkey.t -> 'a Ienv.Key.t) (input_env : Ienv.t) (default : 'a) : 'a m =
  let* step = step in
  let key = make_key (Stepkey step) in
  match Ienv.find key input_env with
  | Some i -> let* () = log_input key i in return i
  | None -> let* () = log_input key default in return default

let run (x : 'a m) : Err.t * State.t =
  match run x State.empty Env.empty with
  | Ok _, state, _ -> Done, state
  | Error e, state, _ -> e, state
