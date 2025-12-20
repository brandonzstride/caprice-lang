
type typing =
  | Ill_typed
  | Exhausted[@warning "-37"] (* unused for now, but will be used later *)
  | Well_typed

let testcase_of_filename (typing : typing) (filename : string) : unit Alcotest.test_case =
  let speed_level = `Quick in
  Alcotest.test_case filename speed_level
  @@ fun () ->
    let pgm = Lang.Parser.parse_file filename in
    let answer = Concolic.Loop.begin_ceval pgm ~options:
      { Concolic.Common.Options.default with do_splay = true }
    in
    let is_correct =
      match typing, answer with
      | Ill_typed, Concolic.Common.Answer.Found_error _
      | Exhausted, Exhausted
      | Well_typed, (Unknown | Exhausted | Exhausted_pruned) -> true
      | _ -> false
    in
    Alcotest.check Alcotest.bool "type check" true is_correct

let find_test_dir () =
  let candidates = [ "test/" ; "../../test/" ; "../../../test/" ] in
  match List.find_opt Sys.file_exists candidates with
  | Some dir -> dir
  | None -> 
      let cwd = Sys.getcwd () in
      failwith ("Cannot find test directory. CWD: " ^ cwd)

let root_dir = find_test_dir ()

let all_caprice_filenames (dir : string) : string list =
  let ls_dir dir =
    Sys.readdir dir
    |> Array.to_list
    |> List.map (Filename.concat dir)
  in
  let rec go acc = function
    | [] -> acc
    | file :: worklist when Filename.check_suffix file "caprice" -> go (file :: acc) worklist
    | dir :: worklist when Sys.is_directory dir -> go acc (ls_dir dir @ worklist)
    | _ :: worklist -> go acc worklist
  in
  go [] [ dir ]

let testdir (dirs : (typing * string) list) : unit Alcotest.test list =
  let ( let+ ) x f = List.map f x in
  let+ typing, dir = dirs in
  dir, 
    let+ testfile = all_caprice_filenames dir in
    let testcase = testcase_of_filename typing testfile in
    testcase

let make_tests (names : string list) : unit Alcotest.test list =
  List.map (Filename.concat root_dir) names
  |> List.map (fun name -> [ Well_typed, name ^ "-well-typed" ; Ill_typed, name ^ "-ill-typed" ])
  |> List.flatten
  |> List.filter (fun (_, file) -> Sys.file_exists file)
  |> testdir

let () = Alcotest.run "typecheck"
  @@ make_tests
    [ "bluejay"
    ; "soft-contract"
    ; "simple"
    ; "programs"
    ; "splaying"
    ]
