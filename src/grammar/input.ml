
exception ExtractionException

module Kind = struct
  type _ t =
    | KBool : bool t
    | KInt : int t
    | KTag : Tag.t t
end

type t =
  | IBool of bool
  | IInt of int
  | ITag of Tag.t
  [@@deriving eq, ord]

let extract_exn (type a) (kind : a Kind.t) (input : t) : a =
  match kind, input with
  | KBool, IBool b -> b
  | KInt, IInt i -> i
  | KTag, ITag t -> t
  | _ -> raise ExtractionException

let extract_opt (type a) (kind : a Kind.t) (input : t) : a option =
  match kind, input with
  | KBool, IBool b -> Some b
  | KInt, IInt i -> Some i
  | KTag, ITag t -> Some t
  | _ -> None

let to_string = function
  | IBool b -> Bool.to_string b
  | IInt i -> Int.to_string i
  | ITag t -> Tag.to_string t
