
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
  | Refutation (v, t) -> Answer.Found_error (Cvalue.Error_messages.refutation v t)
  | Confirmation -> Exhausted
  | Mismatch msg -> Found_error msg
  | Assert_false -> Found_error "Failed assertion"
  | Vanish -> Exhausted
  | Unbound_variable Ident id -> Found_error ("Unbound variable: " ^ id)
  | Reach_max_step _step -> Exhausted_pruned
  | Done -> Exhausted

let is_signal_to_stop res = Answer.is_signal_to_stop @@ to_answer res
