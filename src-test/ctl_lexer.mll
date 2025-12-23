{
  open Ctl_parser
  open Lexing
  let incr_lineno lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

let newline = ('\013'* '\010')
let blank = [' ' '\009' '\012']
let identchar = ['A'-'Z' 'a'-'z' '_' '.' '-' '\'' '0'-'9']
let num = ['0'-'9']
let comment = '#' [^'\n']* '\n'

rule is_test = parse
  | blank * { is_test lexbuf }
  | newline { Lexing.new_line lexbuf; is_test lexbuf }
  | "(*" blank* "TEST" { true }
  | _ { false }
  | eof { false }

and token = parse
  | blank *            { token lexbuf }
  | newline            { Lexing.new_line lexbuf; token lexbuf }
  | comment            { incr_lineno lexbuf; token lexbuf }
  | "(*" blank* "TEST" { CTL_BEGIN }
  | "*)"               { CTL_END }
  | "+="               { PLUSEQUAL }
  | "="                { EQUAL }
  | "include"          { INCLUDE }
  | "typecheck"        { TYPECHECK }
  | "skip"             { SKIP }
  | identchar* as s    { IDENTIFIER s }
  | ";"                { SEMI }
  | '"'                { STRING (string "" lexbuf )}
  | eof                { failwith "unexpected eof" }

and string acc = parse
  | [^ '\\' '"' ]+
    { string (acc ^ Lexing.lexeme lexbuf) lexbuf }
  | '\\' newline blank* ('\\' (blank as blank))?
    { let space =
        match blank with None -> "" | Some blank -> String.make 1 blank
      in
      Lexing.new_line lexbuf;
      string (acc ^ space) lexbuf }
  | '\\'
    {string (acc ^ "\\") lexbuf}
  | '"'
    {acc}
