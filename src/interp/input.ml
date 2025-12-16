
exception ExtractionException

type t =
  | IBool of bool
  | IInt of int
  | ILabel of Label.t
  [@@deriving eq, ord]

let bool_opt = function
  | IBool b -> Some b
  | _ -> None

let int_opt = function
  | IInt i -> Some i
  | _ -> None

let label_opt = function
  | ILabel l -> Some l
  | _ -> None

let bool_exn = function
  | IBool b -> b
  | _ -> raise ExtractionException

let int_exn = function
  | IInt i -> i
  | _ -> raise ExtractionException

let label_exn = function
  | ILabel l -> l
  | _ -> raise ExtractionException

let to_string = function
  | IBool b -> Bool.to_string b
  | IInt i -> Int.to_string i
  | ILabel l -> Label.to_string l
