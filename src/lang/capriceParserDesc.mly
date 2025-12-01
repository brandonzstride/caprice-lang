%{
  (*
  open Ast
  open Binop
  open Pattern
  *)
%}

%token <string> IDENTIFIER
%token <int> INT
%token <bool> BOOL
%token EOF
%token OPEN_BRACE
%token CLOSE_BRACE
%token OPEN_PAREN
%token CLOSE_PAREN
%token SEMICOLON
%token BACKTICK
%token EQUALS
%token DOT
%token COLON
%token UNDERSCORE
%token PIPE
%token DOUBLE_PIPE
%token DOUBLE_AMPERSAND
%token NOT
%token FUNCTION
%token WITH
%token IF
%token THEN
%token ELSE
%token LET
%token IN
%token ARROW
%token MATCH
%token END
%token STRUCT
%token DEFER
%token PLUS
%token MINUS
%token ASTERISK
%token SLASH
%token PERCENT
%token EQUAL_EQUAL
%token NOT_EQUAL
%token LESS
%token LESS_EQUAL
%token GREATER
%token GREATER_EQUAL
%token PIPELINE
%token LONG_ARROW
%token BOOL_KEYWORD
%token BOTTOM_KEYWORD
%token INPUT
%token INT_KEYWORD
%token MU
%token OF
%token SIG
%token SINGLETYPE_KEYWORD
%token TOP_KEYWORD
%token TYPE
%token UNIT_KEYWORD
%token VAL
%token OPEN_BRACKET
%token CLOSE_BRACKET
%token DOUBLE_COLON
%token AND
%token ASSERT
%token ASSUME
%token DEPENDENT
%token DEP
%token LIST
%token REC
%token ABSTRACT

/*
 * Precedences and associativities.  Lower precedences come first.
 */
%nonassoc prec_let prec_fun   /* Let-ins and functions */
%nonassoc prec_if             /* Conditionals */
%nonassoc prec_mu             /* mu types */
%left PIPELINE                /* |> */
%right DOUBLE_PIPE            /* || for boolean or */
%right DOUBLE_AMPERSAND       /* && for boolean and */
%right NOT                    /* Not */
/* == <> < <= > >= */
%left EQUAL_EQUAL NOT_EQUAL LESS LESS_EQUAL GREATER GREATER_EQUAL
%right DOUBLE_COLON           /* :: */
%left PLUS MINUS              /* + - */
%left ASTERISK SLASH PERCENT  /* * / % */
%left AMPERSAND
%right prec_variant           /* variants, lists */
%right ARROW LONG_ARROW       /* -> for type declaration, and --> for deterministic */

%start <int list> prog
%start <int list option> delim_expr

%%

prog:
  | statement_list EOF { $1 }
  ;

delim_expr:
  | EOF
      { None }
  | prog EOF
      { Some ($1) }
  ;

statement_list:
  | statement { [ $1 ] }
  | statement statement_list { $1 :: $2 }

statement:
  | UNIT_KEYWORD { 0 }
