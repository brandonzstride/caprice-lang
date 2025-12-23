
open Ctl_ast
open Variables

type t = Preset of Ident.t [@@unboxed]

let s (Ident.Ident id) = id

(*
  Preset: splaying can quickly prove this well typed
*)
let exhaustible : Ctl_ast.t =
  [ Env_stmt (Assign (speed, s fast))
  ; Env_stmt (Assign (typing, s exhausted))
  ; Env_stmt (Append (flags, " -s")) 
  ; Test Typecheck
  ]

(*
  Preset: there is a refutation, i.e. a path that shows the program is ill-typed
*)
let refutable : Ctl_ast.t =
  [ Env_stmt (Assign (speed, s fast))
  ; Env_stmt (Assign (typing, s ill_typed))
  ; Test Typecheck
  ]

(*
  Preset: there are naturally finitely many paths
*)
let finitely_exhaustible : Ctl_ast.t =
  [ Env_stmt (Assign (speed, s fast))
  ; Env_stmt (Assign (typing, s exhausted))
  ; Test Typecheck
  ]

let lookup : ident -> Ctl_ast.t = function
  | Ident "finitely-exhaustible" -> finitely_exhaustible
  | Ident "exhaustible" -> exhaustible
  | Ident "refutable" -> refutable
  | _ -> []
