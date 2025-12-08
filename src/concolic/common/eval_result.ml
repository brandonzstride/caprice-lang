
type t =
  | Val of Cvalue.any * Stepkey.t
  | Res of Check_result.t
