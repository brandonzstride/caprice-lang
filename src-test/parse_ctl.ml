
open Lexing

exception Parse_error of exn * int * int * string * string

let propagate_parse_error buf filename f =
  try f ()
  with exn ->
    let curr = buf.lex_curr_p in
    let line = curr.pos_lnum in
    let column = curr.pos_cnum - curr.pos_bol in
    let tok = lexeme buf in
    raise @@ Parse_error (exn, line, column, tok, filename)

let has_test filename =
  let input = In_channel.open_bin filename in
  let buf = Lexing.from_channel input in
  let b = Ctl_lexer.is_test buf in
  In_channel.close input;
  b

let parse_test_header (filename : string) : Ctl_ast.t option =
  if not (has_test filename) then
    None
  else begin
    let input = In_channel.open_bin filename in
    let buf = Lexing.from_channel input in
    let res =
      propagate_parse_error buf filename @@ fun () ->
      Some (Ctl_parser.ctl_script Ctl_lexer.token buf)
    in
    In_channel.close input;
    res
  end
