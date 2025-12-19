
let typecheck_main =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info "typecheck") @@
  let open Cmdliner.Term.Syntax in
  let+ caprice_pgm = Lang.Parser.parse_program_from_argv
  and+ do_splay = 
    let open Cmdliner.Arg in
    value & flag & info ["s"] ~docv:"FILE" ~doc:"Input filename"
  in
  Concolic.Loop.begin_ceval caprice_pgm ~do_splay

let () = 
  match Cmdliner.Cmd.eval_value' typecheck_main with
  | `Ok _ -> ()
  | `Exit i -> exit i
