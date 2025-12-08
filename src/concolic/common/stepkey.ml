
open Interp

module T = struct
  type t = Stepkey of Step.t [@@unboxed]
    [@@deriving eq, ord]

  let uid (Stepkey step) = Step.uid step
end

include T

module Symb = Smt.Symbol.Make (T)

let int_symbol step = Smt.Formula.symbol (Symb.make_int (Stepkey step))

let bool_symbol step = Smt.Formula.symbol (Symb.make_bool (Stepkey step))
