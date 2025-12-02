
type 'k t = { value : 'a. ('a, 'k) Symbol.t -> 'a option }

let merge (s1 : 'k t) (s2 : 'k t) : 'k t = 
  let value : type a. (a, 'k) Symbol.t -> a option = fun sym ->
    match s1.value sym with
    | None -> s2.value sym
    | v -> v
  in
  { value }

let empty : 'k t = { value = fun _ -> None }
