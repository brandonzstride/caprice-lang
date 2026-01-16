
(* Difference lists *)

type 'a t = 'a list -> 'a list  

let empty : 'a t = fun ls -> ls

let ( -:: ) a dls =
  fun ls -> a :: dls ls

let ( -@ ) dls1 dls2 =
  fun ls -> dls1 (dls2 ls)

let to_list dls = dls []