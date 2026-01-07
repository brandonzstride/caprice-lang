
open Lang
open Grammar

exception InvariantException of string

module State = struct
  type t = 
    { rev_stem : Path.t (* we will cons to the path instead of union a log *)
    ; logged_inputs : Input_env.t 
    ; path_len : Path_length.t (* total length of the path to this point (up to and including the stem) *)
    ; runs : Logged_run.t Utils.Diff_list.t
    ; lazy_values : Lazy_val.t Val.SymbolMap.t
    }

  let empty : t =
    { rev_stem = Path.empty
    ; logged_inputs = Input_env.empty
    ; path_len = Path_length.zero
    ; runs = Utils.Diff_list.empty
    ; lazy_values = Val.SymbolMap.empty
    }
end

module Context = struct
  type t =
    { target : Target.t } 
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

(* We will also want to log this tag in input env, but at what time? *)
let push_tag (tag : Tag.With_alt.t) : (unit, 'env) m =
  let* step = step in
  let* { target } = read_ctx in
  modify (fun s -> 
    { s with rev_stem = 
      if Path_length.geq s.path_len (Target.path_length target) then
        Path.cons_tag tag (Stepkey step) s.rev_stem 
      else
        s.rev_stem
    ; path_len = Path_length.plus_int s.path_len (Tag.priority tag.main) }
  )

(* Pushes the tag to the path and logs it in input environment *)
let push_and_log_tag (tag : Tag.t) : (unit, 'env) m =
  let* step = step in
  let* { target } = read_ctx in
  modify (fun s -> 
    { s with rev_stem =
      if Path_length.geq s.path_len (Target.path_length target) then
        Path.cons_tag { main = tag ; alts = [] } (Stepkey step) s.rev_stem 
      else
        s.rev_stem
    ; path_len = Path_length.plus_int s.path_len (Tag.priority tag)
    ; logged_inputs = Input_env.add (KTag (Stepkey step)) tag s.logged_inputs
    }
  )

let push_formula ?(allow_flip : bool = true) (formula : (bool, Stepkey.t) Smt.Formula.t) : (unit, 'env) m =
  if Smt.Formula.is_const formula
  then return ()
  else
    let* step = step in
    let* { target } = read_ctx in
    modify (fun s -> 
      { s with rev_stem =
        if Path_length.geq s.path_len (Target.path_length target) then
          if allow_flip then
            Path.cons_formula formula (Stepkey step) s.rev_stem
          else
            Path.cons_nonflipping formula s.rev_stem 
        else
          s.rev_stem
      ; path_len = Path_length.plus_int s.path_len 1 }
    )

let log_input (key : 'a Input_env.Key.t) (input : 'a) : (unit, 'env) m =
  modify (fun s -> { s with logged_inputs = Input_env.add key input s.logged_inputs })

let read_input (make_key : Stepkey.t -> 'a Input_env.Key.t) (input_env : Input_env.t) : ('a option, 'env) m =
  let* step = step in
  let key = make_key (Stepkey step) in
  return (Input_env.find key input_env)

let read_and_log_input_with_default (make_key : Stepkey.t -> 'a Input_env.Key.t) 
  (input_env : Input_env.t) ~(default : 'a) : ('a, 'env) m =
  let* step = step in
  let key = make_key (Stepkey step) in
  match Input_env.find key input_env with
  | Some i -> let* () = log_input key i in return i
  | None -> let* () = log_input key default in return default

(*
  Must inline definitions in order to skirt the value restriction.
*)
let target_to_here : 'env. (Target.t, 'env) m =
  { run = fun ~reject:_ ~accept state step _ { target } ->
    accept (
      Target.make Formula.trivial
        (Formula.BSet.union target.all_formulas (Path.formulas state.rev_stem))
        state.logged_inputs
        ~path_length:state.path_len
    ) state step
  }

let fork (forked_m : (Eval_result.t, 'env) u) : (unit, 'env) m =
  let* target = target_to_here in
  let* s = get in
  let* ctx = read_ctx in
  assert (
    let Len n = s.path_len in
    let Len n' = Target.path_length ctx.target in
    n = n' + List.fold_left (fun acc punit ->
      acc + Path.priority_of_punit punit
      ) 0 s.rev_stem
  );
  fork forked_m { target }
    ~setup_state:(fun state ->
      (* keeps all the logged runs *)
      { state with rev_stem = Path.empty }
    )
    ~restore_state:(fun e ~og ~forked_state ->
      { og with runs =
        let forked_run =
          { Logged_run.rev_stem = forked_state.rev_stem 
          ; inputs = forked_state.logged_inputs 
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
let find_symbol (symbol : Val.symbol) : (Lazy_val.t, 'env) m =
  let* { lazy_values ; _ } = get in
  return (Val.SymbolMap.find symbol lazy_values)

let add_symbol (symbol : Val.symbol) (lazy_v : Lazy_val.t) : (unit, 'env) m =
  modify (fun s -> { s with lazy_values = Val.SymbolMap.add symbol lazy_v s.lazy_values })

(* Makes a new symbol for this lazy value. Assumes the lazy value is not a symbol itself *)
let make_new_lazy_value (lgen : Lazy_val.LGen.t) : (Val.any, 'env) m =
  let* Step id = step in (* use step as fresh identifier *)
  let* () = add_symbol { id } (LLazy lgen) in
  return (Val.Any (VLazy { symbol = { id } ; wrapping_types = [] }))

let run' (x : ('a, Val.Env.t) m) (target : Target.t) (s : State.t) (e : Val.Env.t) : Eval_result.t * State.t =
  match run x s e { target } with
  | Ok _, state, _ -> Done, state
  | Error e, state, _ -> e, state

let run (x : ('a, Val.Env.t) m) (target : Target.t) : Eval_result.t * State.t =
  run' x target State.empty Env.empty
