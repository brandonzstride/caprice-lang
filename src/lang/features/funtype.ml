
type det
type nondet

type sort =
  | Det
  | Nondet
  [@@deriving eq, ord]

type ('dom, 'cod) t = { domain : 'dom ; codomain : 'cod ; sort : sort }
  [@@deriving eq, ord]
