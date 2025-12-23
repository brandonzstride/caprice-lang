
module Ident = struct
  module T = struct
    type t = Ident of string [@@unboxed]
      [@@deriving eq, ord]
  end

  include T

  module Map = Baby.H.Map.Make (T)
end

type ident = Ident.t

open Ident

let typing_s = "typing"
let speed_s = "speed"
let fast_s = "fast"
let slow_s = "slow"
let exhausted_s = "exhausted"
let ill_typed_s = "ill-typed"
let no_error_s = "no-error"
let flags_s = "flags"

let typing = Ident typing_s
let speed = Ident speed_s
let fast = Ident fast_s
let slow = Ident slow_s
let exhausted = Ident exhausted_s
let ill_typed = Ident ill_typed_s
let no_error = Ident no_error_s
let flags = Ident flags_s
