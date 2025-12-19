
open Lang

module Make (State : Utils.Types.T) (Env : Env.S) (Ctx : Utils.Types.T) (Err : sig
  type t
  val fail_on_fetch : Ident.t -> State.t -> t * State.t
  val fail_on_max_step : Step.t -> State.t -> t * State.t
end) = struct

  type ('a, 'e) t = {
    run : 'r.
      reject:('e -> State.t -> Step.t -> 'r) ->
      accept:('a -> State.t -> Step.t -> 'r) ->
      State.t -> Step.t -> Env.t -> Ctx.t -> 'r
  }

  let[@inline always][@specialise] bind (x : ('a, 'e) t) (f : 'a -> ('b, 'e) t) : ('b, 'e) t =
    { run =
        fun ~reject ~accept state step env ctx ->
          x.run state step env ctx ~reject ~accept:(fun x state step ->
              (f x).run ~reject ~accept state step env ctx
            )
    }

  let ( let* ) = bind

  let[@inline always][@specialise] return (a : 'a) : ('a, 'e) t =
    { run = fun ~reject:_ ~accept state step _ _ -> accept a state step }

  type 'a m = ('a, Err.t) t (* m is for "monad": it includes an error monad *)

  type 'a s = ('a, Utils.Empty.t) t (* s for "safe": it cannot error *)

  type 'e u = (Utils.Empty.t, 'e) t (* u for "unsafe": it always errors *)


  let make_unsafe (x : 'a s) : ('a, 'e) t =
    { run = fun ~reject:_ ~accept state step env ctx ->
          x.run state step env ctx ~reject:Utils.Empty.absurd ~accept
    }

  (*
    -----------
    ENVIRONMENT
    -----------
  *)

  let read : (Env.t, 'e) t =
    { run = fun ~reject:_ ~accept state step env _ -> accept env state step }

  let[@inline always][@specialise] local (f : Env.t -> Env.t) (x : ('a, 'e) t) : ('a, 'e) t =
    { run = fun ~reject ~accept state step env -> x.run ~reject ~accept state step (f env) }

  (*
    -------
    CONTEXT
    -------
  *)

  let read_ctx : (Ctx.t, 'e) t =
    { run = fun ~reject:_ ~accept state step _ ctx -> accept ctx state step }

  let[@inline always][@specialise] local_ctx (f : Ctx.t -> Ctx.t) (x : ('a, 'e) t) : ('a, 'e) t =
    { run = fun ~reject ~accept state step env ctx -> x.run ~reject ~accept state step env (f ctx) }

  (*
    -----
    STATE
    -----
  *)

  let get : (State.t, 'e) t =
    { run = fun ~reject:_ ~accept state step _ _ -> accept state state step }

  let[@inline always][@specialise] modify (f : State.t -> State.t) : (unit, 'e) t =
    { run =
        fun ~reject:_ ~accept state step _ _ ->
          accept () (f state) step
    }

  (*
    -----
    ERROR
    -----
  *)

  let[@inline always][@specialise] fail (env : Err.t) : 'a m =
    { run = fun ~reject ~accept:_ state step _ _ -> reject env state step }

  let fail_map (f : State.t -> Err.t * State.t) : 'a m = 
    { run = fun ~reject ~accept:_ state step _ _ -> let e, s = f state in reject e s step }

  let[@inline always] handle_error (x : ('a, 'e1) t) (ok : 'a -> ('b, 'e2) t) (err : Err.t -> ('b, 'e2) t) : ('b, 'e2) t =
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

  let run (x : 'a m) (init_state : State.t) (init_env : Env.t) (init_ctx : Ctx.t) : ('a, Err.t) result * State.t * Step.t =
    x.run init_state Step.zero init_env init_ctx
      ~reject:(fun e state step -> Error e, state, step) 
      ~accept:(fun a state step -> Ok a, state, step)

  let run_safe (x : 'a s) (init_state : State.t) (init_env : Env.t) (init_ctx : Ctx.t) : 'a * State.t * Step.t =
    x.run init_state Step.zero init_env init_ctx
      ~reject:Utils.Empty.absurd
      ~accept:(fun a state step -> a, state, step)

  let run_unsafe (x : 'e u) (init_state : State.t) (init_env : Env.t) (init_ctx : Ctx.t) : 'e * State.t * Step.t =
    x.run init_state Step.zero init_env init_ctx
      ~accept:Utils.Empty.absurd
      ~reject:(fun a state step -> a, state, step)

  (*
    -----------------
    INTERPRETER STUFF
    -----------------
  *)

  let step : (Step.t, 'e) t =
    { run = fun ~reject:_ ~accept state step _ _ -> accept step state step }

  let[@inline always] incr_step ~(max_step : Step.t) : unit m = 
    { run = fun ~reject ~accept state step _ _ ->
        let step = Step.next step in
        if Step.(step > max_step)
        then let e, s = Err.fail_on_max_step step state in reject e s step
        else accept () state step
    }

  let[@inline always] fetch (id : Ident.t) : Env.value m =
    { run = fun ~reject ~accept state step env _ ->
        match Env.find id env with
        | None -> let e, s = Err.fail_on_fetch id state in reject e s step
        | Some v -> accept v state step
    }

  let[@inline always] fork (m : 'e u) (fork_ctx : Ctx.t) (k : 'e -> 'a m)
    ~(setup_state : State.t -> State.t) ~(restore_state : og:State.t -> forked_state:State.t -> State.t) 
    : 'a m =
    { run = fun ~reject ~accept state step env ctx ->
      m.run (setup_state state) step env fork_ctx
        ~accept:Utils.Empty.absurd
        ~reject:(fun e forked_state _ -> 
          (* uses original step count when resuming, not step count after fork *)
          (k e).run ~reject ~accept (restore_state ~og:state ~forked_state) step env ctx
        )
    }
end
