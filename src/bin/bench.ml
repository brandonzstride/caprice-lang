
let make_one ~options fname =
  try 
    let pgm = Lang.Parser.parse_file fname in
    let run pgm =
      match
        Concolic.Loop.begin_ceval pgm
          ~print_outcome:false 
          ~options
      with
      | Grammar.Answer.Timeout _ -> assert false
      | _ -> ()
    in
    Some (Filename.basename fname, run, pgm)
  with
  | Lang.Parser.Parse_error _ -> None

let bench_many ~trials tests =
  Benchmark.latencyN (Int64.of_int trials) tests

let ls_dir dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.map (Filename.concat dir)
  |> List.sort String.compare

let is_caprice_file fname = Filename.check_suffix fname "caprice"

let find_caprice_files ~(recpaths : bool) (init : string list) : string list =
  if not recpaths then
    List.flatten @@
    List.map (fun fname ->
      if Sys.is_directory fname then
        List.filter is_caprice_file (ls_dir fname)
      else if is_caprice_file fname then
        [ fname ]
      else
        []
    ) init
  else
    let rec go = function
      | [] -> []
      | dir :: worklist when Sys.is_directory dir ->
        go (ls_dir dir @ worklist)
      | fname :: worklist when is_caprice_file fname ->
        fname :: go worklist
      | _ :: worklist ->
        go worklist
    in
    go init

let bench_main =
  Cmdliner.Cmd.v (Cmdliner.Cmd.info "bench") @@
  let open Cmdliner.Term.Syntax in
  let+ paths = Cmdliner.Arg.(
      non_empty & pos_all file [] &
      info [] ~docv:"PATH" ~doc:"Input files or directories"
    )
  and+ recpaths = Cmdliner.Arg.(
      value & flag &
      info ["recpaths"] ~doc:"Recursively search directories for files"
    )
  and+ options = Concolic.Options.of_argv
  and+ trials = Cmdliner.Arg.(
      value & opt int 200
      & info ["trials"] ~docv:"TRIALS" ~doc:"Number of trials"
    )
  in
  let tests = find_caprice_files ~recpaths paths |> List.filter_map (make_one ~options) in
  let _res = bench_many ~trials tests in
  ()

let () = 
  match Cmdliner.Cmd.eval_value' bench_main with
  | `Ok _ -> ()
  | `Exit i -> exit i
