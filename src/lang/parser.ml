
open Lexing

exception Parse_error of exn * int * int * string

let handle_parse_error buf f =
  try f ()
  with exn ->
    let curr = buf.lex_curr_p in
    let line = curr.pos_lnum in
    let column = curr.pos_cnum - curr.pos_bol in
    let tok = lexeme buf in
    raise @@ Parse_error (exn, line, column, tok)

let parse_program (input : in_channel) : Ast.statement list =
  let buf = Lexing.from_channel input in
  handle_parse_error buf @@ fun () ->
  CapriceParserDesc.prog CapriceLexerDesc.token buf

let parse_file (filename : string) : Ast.statement list =
  parse_program @@ In_channel.open_bin filename

let parse_program_from_argv =
  let open Cmdliner.Term.Syntax in
  let+ src_file = 
    let open Cmdliner.Arg in
    required & pos 0 (some' file) None & info [] ~docv:"FILE" ~doc:"Input filename"
  in
  parse_file src_file
