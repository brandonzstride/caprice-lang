%{
  open Ctl_ast
  open Variables.Ident
%}

%token CTL_BEGIN
%token CTL_END
%token PLUSEQUAL
%token EQUAL
%token INCLUDE
%token TYPECHECK
%token SKIP
%token SEMI
%token <string> IDENTIFIER
%token <string> STRING

%start ctl_script
%type <Ctl_ast.t> ctl_script

%%

ctl_script:
  | CTL_BEGIN ctl_items CTL_END { $2 }

ctl_items:
  | { [] }
  | ctl_item SEMI ctl_items { $1 :: $3 }

ctl_item:
  | test_item { Test $1 }
  | env_item  { Env_stmt $1 }

test_item:
  | TYPECHECK { Typecheck }
  | SKIP      { Skip }

env_item:
  | ident EQUAL string     { Assign ($1, $3) }
  | ident PLUSEQUAL string { Append ($1, $3) }
  | INCLUDE ident         { Include $2 }

ident:
  | IDENTIFIER { Ident $1 }

string:
  | STRING     { $1 }
  | IDENTIFIER { $1 } (* allow non-quoted strings *)
