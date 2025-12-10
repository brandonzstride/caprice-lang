
let typecheck_main =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info "typecheck") @@
  let open Cmdliner.Term.Syntax in
  let+ caprice_pgm = Lang.Parser.parse_program_from_argv in
  let expr = Lang.Ast.t_of_statement_list caprice_pgm in
  Concolic.Loop.begin_ceval expr

let () = 
  match Cmdliner.Cmd.eval_value' typecheck_main with
  | `Ok _ -> ()
  | `Exit i -> exit i
