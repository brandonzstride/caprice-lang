
type t =
  { max_tree_depth : int
  ; max_step       : Interp.Step.t
  ; global_timeout : Mtime.Span.t
  ; do_splay       : bool
  ; is_random      : bool
  }  

let default : t =
  { max_tree_depth = 30
  ; max_step       = Step 100_000
  ; global_timeout = Mtime.Span.(10 * s)
  ; do_splay       = false
  ; is_random      = false
  }  

let of_argv =
  let open Cmdliner.Term.Syntax in
  let open Cmdliner.Arg in
  let+ max_tree_depth =
    value & opt int default.max_tree_depth
    & info ["d"; "depth"] ~docv:"DEPTH" ~doc:"Maximum tree depth"
  and+ max_step =
    value & opt Interp.Step.argv_step_conv default.max_step
    & info ["m"; "max-step"] ~docv:"MAX_STEP" ~doc:"Maximum step count per evaluation"
  and+ global_timeout =
    value & opt Utils.Time.argv_span_conv default.global_timeout
    & info ["t"; "timeout"] ~docv:"TIMEOUT" ~doc:"Global timeout seconds"
  and+ do_splay = 
    value & flag & info ["s"; "splay"] ~doc:"Do type splay"
  and+ is_random = 
    value & flag & info ["r"; "random"] ~doc:"Randomize"
  in
  { max_tree_depth ; max_step ; global_timeout ; do_splay ; is_random }

