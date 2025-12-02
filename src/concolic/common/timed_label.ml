
module T = struct
  type 'k t = { time : 'k ; label : Label.t }
end

include T

module With_alt = struct
  type 'k t = { time : 'k ; label : Label.With_alt.t }
end
