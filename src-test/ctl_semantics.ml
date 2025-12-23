
open Ctl_ast
open Variables

type test_expect = 
  | Ill_typed (* type refutation found *)
  | Exhausted (* provably well-typed *)
  | No_error  (* no type refutation, and no well-typedness proof *)

let parse_expect = function
  | "ill-typed" -> Ill_typed
  | "no-error" -> No_error
  | "exhausted" | _ -> Exhausted

let parse_speed = function
  | "slow" -> `Slow
  | "fast" | _ -> `Quick

let interp_env (env : Environment.t) (ast : Ctl_ast.t) : Environment.t * testkind =
  let testkind = ref Typecheck in
  let rec interp env ast = 
    List.fold_left (fun env -> function
      | Env_stmt Assign (id, s) ->
        Ident.Map.add id s env
      | Env_stmt Append (id, s) ->
        Ident.Map.update id (function 
          | Some s' -> Some (s' ^ s) 
          | None -> Some s
        ) env
      | Env_stmt Include s ->
        interp env (Preset.lookup s)
      | Test kind ->
        testkind := kind;
        env
    ) env ast
  in
  let e = interp env ast in
  e, !testkind

let get_var env var default = 
  Ident.Map.find_opt var env
  |> Option.value ~default

let options_of_env (env : Environment.t) : Concolic.Common.Options.t =
  let flags_str = get_var env flags "" in
  let argv = String.split_on_char ' ' flags_str |> Array.of_list in
  let cmd = Cmdliner.Cmd.v (Cmdliner.Cmd.info "parseflags") Concolic.Common.Options.of_argv in
  match Cmdliner.Cmd.eval_value ~argv cmd with
  | Ok (`Ok options) -> options
  | Ok `Version -> failwith "version requested"
  | Ok `Help -> failwith "help requested"
  | Error _ -> failwith "parse error"

let compute_typecheck_test filename env = 
  let expect = parse_expect (get_var env typing exhausted_s) in
  let options = options_of_env env in
  let pgm = Lang.Parser.parse_file filename in
  let answer = Concolic.Loop.begin_ceval pgm ~options in
  match expect, answer with
  | Ill_typed, Concolic.Common.Answer.Found_error _
  | Exhausted, Exhausted
  | No_error, (Unknown | Exhausted_pruned | Timeout _) -> true
  | _ -> false

let check_true msg b =
  Alcotest.(check bool msg true b)

let make_test (filename : string) : unit Alcotest.test_case option =
  match Parse_ctl.parse_test_header filename with
  | None -> None
  | Some ctl_script ->
    let env, testkind = interp_env Environment.default ctl_script in
    let speed_level = parse_speed (get_var env speed fast_s) in
    Option.some @@
    Alcotest.test_case filename speed_level (fun () ->
      match testkind with
      | Skip ->
        Alcotest.skip ()
      | Typecheck ->
        check_true "failed type check" @@
        compute_typecheck_test filename env
    )
