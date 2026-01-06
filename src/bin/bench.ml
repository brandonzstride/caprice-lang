
let bench_one ?name ~options ~trials fname =
  Benchmark.latency1
    ~name:(Option.value name ~default:(Filename.basename fname))
    (Int64.of_int trials)
    (Concolic.Loop.begin_ceval
      ~print_outcome:false 
      ~options)
    (Lang.Parser.parse_file fname)

let bench_main =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info "bench") @@
  let open Cmdliner.Term.Syntax in
  let+ filename = Cmdliner.Arg.(
      required & pos 0 (some' file) None & info [] ~docv:"FILE" ~doc:"Input filename"
    )
  and+ options = Concolic.Options.of_argv
  and+ trials = Cmdliner.Arg.(
      value & opt int 200 & info ["trials"] ~docv:"TRIALS" ~doc:"Number of trials"
    )
  in
  let res = bench_one ~options ~trials filename in
  Format.printf "\n";
  Benchmark.tabulate res;
  Format.printf "\n";
  Benchmark.print_gc res

let () = 
  match Cmdliner.Cmd.eval_value' bench_main with
  | `Ok _ -> ()
  | `Exit i -> exit i
