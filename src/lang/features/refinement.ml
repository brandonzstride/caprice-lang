
type ('a, 'p) t = { var : Ident.t ; tau : 'a ; predicate : 'p }
  [@@deriving eq, ord]
