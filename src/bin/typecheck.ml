
let typecheck_main =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info "typecheck") @@
  let open Cmdliner.Term.Syntax in
  let open Cmdliner.Arg in
  let+ caprice_pgm = Lang.Parser.parse_program_from_argv
  and+ do_splay = 
    value & flag & info ["s"] ~docv:"FILE" ~doc:"Input filename"
  and+ timeout =
    value & opt (some float) None & info ["t"] ~docv:"TIMEOUT" ~doc:"Global timeout seconds"
  in
  Concolic.Loop.begin_ceval 
    ?timeout:(Option.bind timeout Utils.Time.of_float_sec)
    ~do_splay
    caprice_pgm

let () = 
  match Cmdliner.Cmd.eval_value' typecheck_main with
  | `Ok _ -> ()
  | `Exit i -> exit i
