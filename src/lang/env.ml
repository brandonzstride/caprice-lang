
type 'a t = 'a Ident.Map.t

let empty = Ident.Map.empty

let find = Ident.Map.find_opt

let set = Ident.Map.add
