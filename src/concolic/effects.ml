
open Lang
open Interp_common
open Common

(* TODO *)
module Input_env = struct type t = I let empty = I end

type k = Step.t

module V = Cvalue.Make (Step)

module State = struct
  type t = 
    { path : k Path.t (* we will cons to the path instead of union a log *)
    ; logged_inputs : Input_env.t }

  let empty : t =
    { path = Path.empty
    ; logged_inputs = Input_env.empty }
end

module Env = V.Env

module Err = struct
  type t = 
    | Refutation of V.data V.t * V.typeval V.t
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

include Effects.Make (State) (Env) (Err)

let vanish : 'a m =
  fail Vanish

let push_label (label : k Timed_label.With_alt.t) : unit m =
  modify (fun s -> { s with path = Path.cons_label label s.path })

let push_branch (formula : (bool, k) Smt.Formula.t) : unit m =
  if Smt.Formula.is_const formula
  then return ()
  else modify (fun s -> { s with path = Path.cons_formula formula s.path })

let run (x : 'a m) : Err.t * k Path.t =
  match run x State.empty Env.empty with
  | Ok _, state, _ -> Done, state.path
  | Error e, state, _ -> e, state.path
