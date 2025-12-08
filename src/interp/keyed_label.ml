
module T = struct
  type 'k t = { key : 'k ; label : Label.t }
    [@@deriving eq, ord]
end

include T

module With_alt = struct
  type 'k t = { key : 'k ; label : Label.With_alt.t }
    [@@deriving eq, ord]
end
