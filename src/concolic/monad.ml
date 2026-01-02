
open Grammar

(*
  Make a monad that has
    - CPS
    - State
    - Environment
    - Context (environment that changes less often)
    - Step count (stateful)
    - Error ("good" and "bad" continuations)

  Just a few interpreter-specific functions are implemented
  (e.g. increment step count and fail on max step).

  The error continuation may be used simply to escape the
  typical continuation, but not always to convey some breaking
  failure case, so it is called with `escape`.
*)
module Make (State : Utils.Types.T) (Ctx : Utils.Types.T) (Err : sig
  type t
  val fail_on_max_step : Step.t -> State.t -> t * State.t
end) = struct

  (*
    The error and environment are type parameters. This way, they can be
    empty or env universally quantified to convey that a certain monadic
    value does not error or does not use the environment.
  *)
  type ('a, 'err, 'env) t = {
    run : 'r.
      reject:('err -> State.t -> Step.t -> 'r) ->
      accept:('a -> State.t -> Step.t -> 'r) ->
      State.t -> Step.t -> 'env -> Ctx.t -> 'r
  } [@@unboxed]
  (* With flambda and compiler flag O3, it is faster to unbox. In all other
    combinations (of regular compiler, O3, flambda without O3), it is faster
    to leave this boxed. *)

  let[@inline always][@specialise] bind
    : 'a 'b 'err 'env. ('a, 'err, 'env) t -> ('a -> ('b, 'err, 'env) t) -> ('b, 'err, 'env) t
    = fun x f ->
    { run =
        fun ~reject ~accept state step env ctx ->
          x.run state step env ctx ~reject ~accept:(fun x state step ->
              (f x).run ~reject ~accept state step env ctx
            )
    }

  let ( let* ) 
    : 'a 'b 'err 'env. ('a, 'err, 'env) t -> ('a -> ('b, 'err, 'env) t) -> ('b, 'err, 'env) t
    = bind

  let[@inline always][@specialise] return
    : 'a 'err 'env. 'a -> ('a, 'err, 'env) t
    = fun a ->
    { run = fun ~reject:_ ~accept state step _ _ -> accept a state step }

  type ('a, 'env) m = ('a, Err.t, 'env) t (* m is for "monad": it includes an error monad *)

  (* type 'a s = ('a, Utils.Empty.t) t s for "safe": it cannot error *)

  type ('err, 'env) u = (Utils.Empty.t, 'err, 'env) t (* u for "unsafe": it always errors *)

  type ('err, 'env) failing = { run_failing : 'a. ('a, 'err, 'env) t } [@@unboxed]

  (* let make_unsafe (x : 'a s) : ('a, 'e) t =
    { run = fun ~reject:_ ~accept state step env ctx ->
          x.run state step env ctx ~reject:Utils.Empty.absurd ~accept
    } *)

  (*
    -----------
    ENVIRONMENT
    -----------
  *)

  let read : 'err 'env. ('env, 'err, 'env) t =
    { run = fun ~reject:_ ~accept state step env _ -> accept env state step }

  let[@inline always][@specialise] local (f : 'env -> 'env) (x : ('a, 'err, 'env) t) : ('a, 'err, 'env) t =
    { run = fun ~reject ~accept state step env -> x.run ~reject ~accept state step (f env) }

  let local'
    : 'env. 'e -> ('a, 'err, 'e) t -> ('a, 'err, 'env) t
    = fun env x ->
    { run = fun ~reject ~accept state step _ -> x.run ~reject ~accept state step env }

  (*
    -------
    CONTEXT
    -------
  *)

  let read_ctx : 'err 'env. (Ctx.t, 'err, 'env) t =
    { run = fun ~reject:_ ~accept state step _ ctx -> accept ctx state step }

  let[@inline always][@specialise] local_ctx (f : Ctx.t -> Ctx.t) (x : ('a, 'err, 'env) t) : ('a, 'err, 'env) t =
    { run = fun ~reject ~accept state step env ctx -> x.run ~reject ~accept state step env (f ctx) }

  (*
    -----
    STATE
    -----
  *)

  let get : 'err 'env. (State.t, 'err, 'env) t =
    { run = fun ~reject:_ ~accept state step _ _ -> accept state state step }

  let[@inline always][@specialise] modify (f : State.t -> State.t) : (unit, 'err, 'env) t =
    { run =
        fun ~reject:_ ~accept state step _ _ ->
          accept () (f state) step
    }

  (*
    -----
    ERROR
    -----
  *)

  let[@inline always][@specialise] escape : 'a 'env. Err.t -> ('a, 'env) m = fun err ->
    { run = fun ~reject ~accept:_ state step _ _ -> reject err state step }

  let[@inline always] handle_error (x : ('a, 'err1, 'env) t) (ok : 'a -> ('b, 'err2, 'env) t)
    (err : Err.t -> ('b, 'err2, 'env) t) : ('b, 'err2, 'env) t =
    { run = fun ~reject ~accept state step env ctx ->
        x.run state step env ctx
          ~reject:(fun a state step ->
              (err a).run ~reject ~accept state step env ctx
            )
          ~accept:(fun a state step ->
              (ok a).run ~reject ~accept state step env ctx
            )
    }

  (*
    ------------------
    ESCAPING THE MONAD
    ------------------
  *)

  let run (x : ('a, 'env) m) (init_state : State.t) (init_env : 'env) (init_ctx : Ctx.t) : ('a, Err.t) result * State.t * Step.t =
    x.run init_state Step.zero init_env init_ctx
      ~reject:(fun e state step -> Error e, state, step) 
      ~accept:(fun a state step -> Ok a, state, step)

  (* let run_safe (x : 'a s) (init_state : State.t) (init_env : Env.t) (init_ctx : Ctx.t) : 'a * State.t * Step.t =
    x.run init_state Step.zero init_env init_ctx
      ~reject:Utils.Empty.absurd
      ~accept:(fun a state step -> a, state, step) *)

  (* let run_unsafe (x : 'e u) (init_state : State.t) (init_env : Env.t) (init_ctx : Ctx.t) : 'e * State.t * Step.t =
    x.run init_state Step.zero init_env init_ctx
      ~accept:Utils.Empty.absurd
      ~reject:(fun a state step -> a, state, step) *)

  (*
    -----------------
    INTERPRETER STUFF
    -----------------
  *)

  let step : (Step.t, 'err, 'env) t =
    { run = fun ~reject:_ ~accept state step _ _ -> accept step state step }

  let[@inline always][@specialise] incr_step 
    : 'env. max_step:Step.t -> (unit, 'env) m
    = fun ~max_step ->
    { run = fun ~reject ~accept state step _ _ ->
        let step = Step.next step in
        if Step.(step > max_step)
        then let e, s = Err.fail_on_max_step step state in reject e s step
        else accept () state step
    }

  let[@inline always][@specialise] fork (m : ('e, 'env) u) (fork_ctx : Ctx.t) (k : 'e -> ('a, 'env) m)
    ~(setup_state : State.t -> State.t) 
    ~(restore_state : 'e -> og:State.t -> forked_state:State.t -> State.t) 
    : ('a, 'env) m =
    { run = fun ~reject ~accept state step env ctx ->
      m.run (setup_state state) step env fork_ctx
        ~accept:Utils.Empty.absurd
        ~reject:(fun e forked_state _ -> 
          (* uses original step count when resuming, not step count after fork *)
          (k e).run ~reject ~accept (restore_state e ~og:state ~forked_state) step env ctx
        )
    }
end
