
open Lang
open Interp

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

let fail_on_fetch (i : Ident.t) (s : 'a) : t * 'a =
  Unbound_variable i, s

let fail_on_max_step (n : Step.t) (s : 'a) : t * 'a =
  Reach_max_step n, s

let to_answer = function
  | Refutation (_v, _t) -> Answer.Found_error "Refutation" (* TODO : pretty print value and type *)
  | Confirmation -> Exhausted
  | Mismatch msg -> Found_error msg
  | Assert_false -> Found_error "Failed assertion"
  | Vanish -> Exhausted
  | Unbound_variable Ident id -> Found_error ("Unbound variable " ^ id)
  | Reach_max_step _step -> Exhausted_pruned
  | Done -> Exhausted

let is_signal_to_stop = function
  | Refutation _ | Mismatch _ | Assert_false | Unbound_variable _ -> true
  | _ -> false
