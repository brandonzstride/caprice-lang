
open Interp

type t = Stepkey of Step.t [@@unboxed]
  [@@deriving eq, ord]

let uid (Stepkey step) = Step.uid step
