
open Lang
open Grammar

exception InvariantException of string

(*
  IMPORTANT:
    We are using some mutable state with Store, so this monad
    will not obey all monad laws because it is not pure. However,
    in every real use, it is fine.

    This is done to keep the state record small and avoid a map
    to lookup stateful values. When the monad is forked, we must
    carefully snapshot the store, and when it is joined back, we
    restore the original store.

    Since this is a code smell, the choice may be reverted in the
    future.
*)
module State = struct
  let store = Store.create ()

  type t = 
    { rev_stem : Rev_stem.t (* we will cons to the path instead of union a log *)
    ; logged_inputs : Input_env.t 
    ; runs : Logged_run.t Utils.Diff_list.t
    }

  let empty : t =
    { rev_stem = Rev_stem.empty
    ; logged_inputs = Input_env.empty
    ; runs = Utils.Diff_list.empty
    }

  let get_cell : 'a. 'a Store.Ref.t -> 'a = fun c -> Store.Ref.get store c
  let set_cell : 'a. 'a Store.Ref.t -> 'a -> unit = fun c a -> Store.Ref.set store c a
  let make_cell : 'a. 'a -> 'a Store.Ref.t = fun a -> Store.Ref.make store a
end

module Context = struct
  type det_context =
    | Allowed
    | Disallowed

  type t =
    { target : Target.t
    ; det_context : det_context }
end

(*
  Make a monad out of the state and context and evaluation result.
  - Has stateful State as well as step count
  - Has a target as a context, and also a type parameter for the environment
  - The error type is from Eval_result
*)
module M = Monad.Make (State) (Context) (Eval_result)
include M

module Matches = Val.Make_match (struct
  type 'a m = ('a, Val.Env.t) M.m
  include (M : Utils.Types.MONAD with type 'a m := 'a m)
end)

let[@inline always] fetch (id : Ident.t) : (Val.any, Val.Env.t) m =
  { run = fun ~reject ~accept state step env _ ->
      match Env.find id env with
      | None -> let e, s = Eval_result.fail_on_fetch id state in reject e s step
      | Some v -> accept v state step
  }

(* For typing purposes (due to value restriction), we must inline the
  definition of `M.escape`.
    
  The ideal implementation would simply be `escape Vanish`.
*)
let vanish : 'a 'env. ('a, 'env) m =
  { run = fun ~reject ~accept:_ state step _ _ -> reject Vanish state step }

let mismatch : 'a 'env. string -> ('a, 'env) m = fun msg ->
  escape (Mismatch msg)

let assert_inputs_allowed : 'env. (unit, 'env) m =
  { run = fun ~reject ~accept state step _ ctx ->
    match ctx.det_context with
    | Allowed -> accept () state step
    | Disallowed -> reject (Mismatch "Nondeterminism used when not allowed") state step
  }

(*
  Pushes the tag to the path.
*)
let push_tag_to_path ?(alternates : Tag.t list = []) (tag : Tag.t) : (unit, 'env) m =
  let* step = step in
  let* { target ; _ } = read_ctx in
  modify (fun s -> 
    { s with rev_stem = 
      Rev_stem.cons (Tag ({ main = tag ; alts = alternates }, Stepkey step, s.logged_inputs)) s.rev_stem
        ~if_exceeds:(Target.path_length target)
    }
  )

(* Pushes the tag to the path and logs it in input environment *)
let push_and_log_tag (tag : Tag.t) : (unit, 'env) m =
  let* step = step in
  let* { target ; _ } = read_ctx in
  modify (fun s -> 
    { s with rev_stem =
      Rev_stem.cons (Tag ({ main = tag ; alts = [] }, Stepkey step, s.logged_inputs)) s.rev_stem
        ~if_exceeds:(Target.path_length target)
    ; logged_inputs = Input_env.add KTag (Stepkey step) tag s.logged_inputs
    }
  )

(*
  Pushes the formula to the path as one that is necessarily true
  to have taken the current path.
*)
let push_formula_to_path ?(allow_flip : bool = true) (formula : (bool, Stepkey.t) Smt.Formula.t) : (unit, 'env) m =
  if Smt.Formula.is_const formula
  then return ()
  else
    let* { target ; _ } = read_ctx in
    modify (fun s -> 
      { s with rev_stem =
        let punit =
          if allow_flip then
            Path_item.Formula (formula, s.logged_inputs)
          else
            Nonflipping formula
        in
        Rev_stem.cons punit s.rev_stem
          ~if_exceeds:(Target.path_length target)
      }
    )

let log_input (kind : 'a Input.Kind.t) (input : 'a) : (unit, 'env) m =
  let* step = step in
  modify (fun s -> { s with logged_inputs = Input_env.add kind (Stepkey step) input s.logged_inputs })

let read_input (kind : 'a Input.Kind.t) (input_env : Input_env.t) : ('a option, 'env) m =
  let* () = assert_inputs_allowed in
  let* step = step in
  return (Input_env.find kind (Stepkey step) input_env)

let read_and_log_input_with_default (kind : 'a Input.Kind.t) (input_env : Input_env.t)
  ~(default : 'a) : ('a, 'env) m =
  let* () = assert_inputs_allowed in
  let* step = step in
  match Input_env.find kind (Stepkey step) input_env with
  | Some i -> let* () = log_input kind i in return i
  | None -> let* () = log_input kind default in return default

(*
  Must inline definitions in order to skirt the value restriction.
*)
let target_to_here : 'env. (Target.t, 'env) m =
  { run = fun ~reject:_ ~accept state step _ { target ; _ } ->
    accept (
      Target.make Formula.trivial
        (Formula.BSet.union target.all_formulas (Path.formulas state.rev_stem.rev_stem))
        state.logged_inputs
        ~path_length:state.rev_stem.total_len
    ) state step
  }

let fork (forked_m : (Eval_result.t, 'env) u) : (unit, 'env) m =
  let* target = target_to_here in
  let* s = get in
  let* ctx = read_ctx in
  assert (
    let n = s.rev_stem.total_len in
    let n' = Target.path_length ctx.target in
    Path_length.geq n n'
  );
  let snapshot = ref None in
  fork forked_m { target ; det_context = ctx.det_context }
    ~setup_state:(fun state ->
      (* keeps all the logged runs *)
      snapshot := Some (Store.capture State.store);
      { state with rev_stem = Rev_stem.of_len state.rev_stem.total_len }
    )
    ~restore_state:(fun e ~og ~forked_state ->
      Store.restore State.store (Option.get !snapshot);
      { og with runs =
        let forked_run =
          { Logged_run.rev_stem = forked_state.rev_stem 
          ; target 
          ; answer = Eval_result.to_answer e }
        in
        let open Utils.Diff_list in
        (* Note that the forked state runs include the original runs (see setup_state) *)
        forked_run -:: forked_state.runs (* ... hence, don't copy the og runs *)
      }
    )
    (fun res ->
      if Eval_result.is_signal_to_stop res
      then escape res (* propagate up the failure *)
      else return ())

(* INVARIANT: the symbol must always exist *)
(* let find_symbol (symbol : Val.symbol) : (Val.vlazy, 'env) m =
  let* { lazy_values ; _ } = get in
  return (Val.SymbolMap.find symbol lazy_values)

let add_symbol (symbol : Val.symbol) (lazy_v : Lazy_val.t) : (unit, 'env) m =
  modify (fun s -> { s with lazy_values = Val.SymbolMap.add symbol lazy_v s.lazy_values })

(* Makes a new symbol for this lazy value. Assumes the lazy value is not a symbol itself *)
let make_new_lazy_value (lgen : Lazy_val.LGen.t) : (Val.any, 'env) m =
  let* Step id = step in (* use step as fresh identifier *)
  let* () = add_symbol { id } (LLazy lgen) in
  return (Val.Any (VLazy { symbol = { id } ; wrapping_types = [] })) *)

let disallow_inputs (x : ('a, 'env) m) : ('a, 'env) m =
  local_ctx (fun ctx -> { ctx with det_context = Disallowed }) x

let allow_inputs (x : ('a, 'env) m) : ('a, 'env) m =
  local_ctx (fun ctx -> { ctx with det_context = Allowed }) x

let run' (x : ('a, Val.Env.t) m) (target : Target.t) (s : State.t) (e : Val.Env.t) : Eval_result.t * State.t =
  match run x s e { target ; det_context = Allowed } with
  | Ok _, state, _ -> Done, state
  | Error e, state, _ -> e, state

let run (x : ('a, Val.Env.t) m) (target : Target.t) : Eval_result.t * State.t =
  run' x target State.empty Env.empty
