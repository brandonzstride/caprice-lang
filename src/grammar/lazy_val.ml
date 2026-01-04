
open Lang

module LGen = struct
  type t =
    | LGenList of Val.tval
    | LGenMu of { var : Ident.t ; closure : Ast.t Val.closure }
end

(*
  See in module Val that lazy values are data values. This is possibly a bad choice
  because when forced, they can become type values. But this is not significantly
  different than how an arbitrary expression evaluates to either a type value or
  data value; we're unsure until we try to evaluate it. Similarly with a lazy
  value. However, there are a few places (like lazily generated lists) where it
  is nicer to store them as data values.
*)
type t =
  | LLazy of LGen.t
  | LValue of Val.any
