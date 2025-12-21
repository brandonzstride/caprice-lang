
type 'k t = 
  { value : 'a. ('a, 'k) Symbol.t -> 'a option
  ; domain : Utils.Uid.t list }

let merge (s1 : 'k t) (s2 : 'k t) : 'k t = 
  let value : type a. (a, 'k) Symbol.t -> a option = fun sym ->
    match s1.value sym with
    | None -> s2.value sym
    | v -> v
  in
  { value
  ; domain = s1.domain @ s2.domain }

let empty : 'k t = { value = (fun _ -> None) ; domain = [] }

let singleton (type a) (a : a) (s : (a, 'k) Symbol.t) : 'k t =
  match s with
  | I uid ->
    let value (type a) (sym : (a, 'k) Symbol.t) : a option =
      match sym with
      | I u when u = uid -> Some a
      | _ -> None
    in
    { value ; domain = [ uid ] }
  | B uid ->
    let value (type a) (sym : (a, 'k) Symbol.t) : a option =
      match sym with
      | B u when u = uid -> Some a
      | _ -> None
    in
    { value ; domain = [ uid ] }
