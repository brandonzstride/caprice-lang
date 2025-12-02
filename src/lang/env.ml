
type 'a t = 'a Ident.Map.t

let empty = Ident.Map.empty

let extend base_env extending_env =
  Ident.Map.union (fun _ _ v -> Some v)
    base_env extending_env

let singleton = Ident.Map.singleton

let find = Ident.Map.find_opt

let set = Ident.Map.add
