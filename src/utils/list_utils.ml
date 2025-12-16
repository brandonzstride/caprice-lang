
let fold_left_until f finish init ls =
  let rec go acc = function
    | [] -> finish acc
    | hd :: tl ->
      match f acc hd with
      | `Stop x -> x
      | `Continue a -> go a tl
  in
  go init ls
