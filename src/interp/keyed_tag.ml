
module T = struct
  type 'k t = { key : 'k ; tag : Tag.t }
    [@@deriving eq, ord]
end

include T

module With_alt = struct
  type 'k t = { key : 'k ; tag : Tag.With_alt.t }
    [@@deriving eq, ord]
end
