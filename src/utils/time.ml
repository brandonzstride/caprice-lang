
let time f x =
  let t0 = Mtime_clock.now () in
  let res = f x in
  let t1 = Mtime_clock.now () in
  Mtime.span t0 t1, res

let of_float_sec float_sec =
  let s_per_ns = Mtime.Span.to_float_ns Mtime.Span.s /. Mtime.Span.to_float_ns Mtime.Span.ns in
  Mtime.Span.of_float_ns (float_sec *. s_per_ns)

let convert_span span ~to_ =
  let ns_per_t = Mtime.Span.to_float_ns Mtime.Span.ns /. Mtime.Span.to_float_ns to_ in
  Mtime.Span.to_float_ns span *. ns_per_t

let span_to_ms = convert_span ~to_:Mtime.Span.ms

let divide_span span n =
  Option.get @@ 
  Mtime.Span.of_float_ns (Mtime.Span.to_float_ns span /. Int.to_float n)

let argv_span_conv =
  Cmdliner.Arg.Conv.make ()
    ~docv:"SPAN_SEC"
    ~parser:(fun s ->
        let span_opt = Option.bind (Float.of_string_opt s) of_float_sec in
        match span_opt with
        | Some span -> Ok span
        | None -> Error "Invalid time span as float seconds"
      )
    ~pp:Mtime.Span.pp
