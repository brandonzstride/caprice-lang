
type t = Step of int [@@unboxed]
  [@@deriving eq, ord]

let zero = Step 0

let[@inline always] next (Step i : t) : t =
  Step (i + 1)

let (>) (Step a) (Step b) = a > b

let uid (Step i) = Utils.Uid.of_int i

let argv_step_conv =
  Cmdliner.Arg.Conv.make ()
    ~docv:"STEP"
    ~parser:(fun s -> 
      match int_of_string_opt s with
      | Some i -> Ok (Step i)
      | None -> Error "Expected integer step"
      )
    ~pp:(fun formatter (Step i) -> Format.pp_print_int formatter i)
