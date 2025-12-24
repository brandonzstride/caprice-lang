
open Ctl_ast
open Variables

type t = Preset of Ident.t [@@unboxed]

let s (Ident.Ident id) = id

(*
  Preset: splaying can quickly prove this well typed
*)
let splayable : Ctl_ast.t =
  [ Env_stmt (Assign (speed, s fast))
  ; Env_stmt (Assign (typing, s exhausted))
  ; Env_stmt (Append (flags, " -s")) (* TODO: add wrap here *)
  ; Test Typecheck
  ]

(*
  Preset: there is a refutation, i.e. a path that shows the program is ill-typed
*)
let refutable : Ctl_ast.t =
  [ Env_stmt (Assign (speed, s fast))
  ; Env_stmt (Assign (typing, s ill_typed))
  ; Env_stmt (Append (flags, " -w"))
  ; Test Typecheck
  ]

(*
  Preset: there are naturally finitely many paths
*)
let finite_well_typed : Ctl_ast.t =
  [ Env_stmt (Assign (speed, s fast))
  ; Env_stmt (Assign (typing, s exhausted))
  ; Env_stmt (Append (flags, " -w"))
  ; Test Typecheck
  ]

let lookup : ident -> Ctl_ast.t = function
  | Ident "finite-well-typed" -> finite_well_typed
  | Ident "splayable" -> splayable
  | Ident "refutable" -> refutable
  | _ -> []
