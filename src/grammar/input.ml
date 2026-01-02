
exception ExtractionException

type t =
  | IBool of bool
  | IInt of int
  | ITag of Tag.t
  [@@deriving eq, ord]

let bool_opt = function
  | IBool b -> Some b
  | _ -> None

let int_opt = function
  | IInt i -> Some i
  | _ -> None

let tag_opt = function
  | ITag t -> Some t
  | _ -> None

let bool_exn = function
  | IBool b -> b
  | _ -> raise ExtractionException

let int_exn = function
  | IInt i -> i
  | _ -> raise ExtractionException

let tag_exn = function
  | ITag t -> t
  | _ -> raise ExtractionException

let to_string = function
  | IBool b -> Bool.to_string b
  | IInt i -> Int.to_string i
  | ITag t -> Tag.to_string t
