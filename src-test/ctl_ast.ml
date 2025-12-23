
(*
  This is the Caprice Test Language, which is very, very
  heavily inspired by the Test Specification Language for
  OCaml.
*)

open Variables

(* 
  Also consider "refute" (no splaying) and "splay only" 
  (don't try a real refutation after splaying).
  
  For now, typecheck means to run the entire front-to-back
  typechecking system, which splays first.
*)
type testkind =
  | Typecheck
  | Skip

type env_stmt = 
  | Assign of ident * string (* variable = value *)
  | Append of ident * string (* variable += value *)
  | Include of ident         (* include variable (an environment preset) *)

type ctl_item =
  | Env_stmt of env_stmt (* environment modifier *)
  | Test of testkind (* test kind *)

type t = ctl_item list
