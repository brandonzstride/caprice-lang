
open Lang
open Common

let eval
  (_expr : Ast.t)
  (_input_env : Ienv.t)
  ~(_max_step : Interp.Step.t)
  : Eval_result.t * Path.t
  = failwith "unimplemented"
