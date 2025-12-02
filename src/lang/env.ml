
module T = struct
  type 'a t = 'a Ident.Map.t

  let empty = Ident.Map.empty

  let extend base_env extending_env =
    Ident.Map.union (fun _ _ v -> Some v)
      base_env extending_env

  let singleton = Ident.Map.singleton

  let find = Ident.Map.find_opt

  let set = Ident.Map.add
end

include T

module type S = sig
  type value
  type t
  val empty : t
  val extend : t -> t -> t
  val singleton : Ident.t -> value -> t
  val find : Ident.t -> t -> value option
  val set : Ident.t -> value -> t -> t
end

module Make (Val : Utils.Types.T) : 
  S with type value = Val.t 
  with type t = Val.t T.t
= struct
  include T
  type value = Val.t 
  type nonrec t = value t
end
