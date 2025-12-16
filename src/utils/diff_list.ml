
(* Difference lists *)

type 'a t = 'a list -> 'a list  

let empty : 'a t = fun ls -> ls

let ( -:: ) a dls =
  fun ls -> dls (a :: ls)

let ( -@ ) dls1 dls2 =
  fun ls -> dls2 (dls1 ls)

let to_list dls = dls []