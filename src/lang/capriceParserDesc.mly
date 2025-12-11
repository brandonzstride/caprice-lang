%{
  open Ast
  open Binop
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
%token COMMA
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
%nonassoc OF                  /* variant type declarations */
%left PIPE                    /* variant type declarations */
%right prec_list_pattern      /* list destruction pattern */
%left COMMA                   /* tuples */
%left PIPELINE                /* |> */
%right DOUBLE_PIPE            /* || for boolean or */
%right DOUBLE_AMPERSAND       /* && for boolean and */
%right NOT                    /* Not */
/* == <> < <= > >= */
%left EQUAL_EQUAL NOT_EQUAL LESS LESS_EQUAL GREATER GREATER_EQUAL
%right DOUBLE_COLON           /* :: */
%right prec_variant_pattern   /* list destruction pattern */
%left PLUS MINUS              /* + - */
%left ASTERISK SLASH PERCENT  /* * / % */
%left AMPERSAND
%right ARROW LONG_ARROW       /* -> for type declaration, and --> for deterministic */

%start <statement list> prog
%start <statement list option> delim_expr

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
  ;

statement:
  | LET l_ident EQUALS expr
    { SUntyped { var = $2 ; defn = $4 } }
  | LET typed_binding EQUALS expr
    { STyped { var = fst $2 ; tau = snd $2 ; defn = $4 } }
  | LET l_ident nonempty_list(l_ident) EQUALS expr
    { SUntyped { var = $2 ; defn =
      List.fold_right (fun param acc ->
        EFunction { param ; body = acc }
      ) $3 $5
    } }
  | LET l_ident nonempty_list(typed_param) COLON expr EQUALS expr
    { STyped { var = $2 ; tau =
      List.fold_right (fun { var = _ ; tau } acc ->
        ETypeFun { domain = tau ; codomain = acc }
      ) $3 $5
    ; defn =
      List.fold_right (fun { var ; tau = _ } acc ->
        EFunction { param = var ; body = acc }
      ) $3 $7
    } }
  ;

%inline typed_binding:
  | l_ident COLON expr
    { ($1, $3) }
  | OPEN_PAREN l_ident COLON expr CLOSE_PAREN
    { ($2, $4) }
  ;

typed_param:
  | OPEN_PAREN l_ident COLON expr CLOSE_PAREN
    { { var = $2 ; tau = $4 } }
  | OPEN_PAREN l_ident COLON expr PIPE expr CLOSE_PAREN
    { { var = $2 ; tau = ETypeRefine { var = $2 ; tau = $4 ; predicate = $6} } }
  // | OPEN_PAREN DEP l_ident COLON expr CLOSE_PAREN
  // | OPEN_PAREN DEPENDENT l_ident COLON expr CLOSE_PAREN
  //   { TVarDep { var = $3 ; tau = $5 } : param }
  // | OPEN_PAREN DEP l_ident COLON expr PIPE expr CLOSE_PAREN
  // | OPEN_PAREN DEPENDENT l_ident COLON expr PIPE expr CLOSE_PAREN
  //   { TVarDep { var = $3 ; tau = ETypeRefinement { tau = $5 ; predicate = EFunction { param = $3 ; body = $7 } } } : param }

expr:
  | appl_expr /* Includes primary expressions */
    { $1 }
  | op_expr
    { $1 }
  | type_expr
    { $1 }
  | expr COMMA expr
    { ETuple ($1, $3) }
  | IF expr THEN expr ELSE expr %prec prec_if
    { EIf { if_ = $2 ; then_ = $4 ; else_ = $6 } }
  | FUNCTION l_ident ARROW expr %prec prec_fun 
    { EFunction { param = $2 ; body = $4 } }
  | statement IN expr %prec prec_let
    { Ast.statement_to_t $1 $3 }
  | MATCH expr WITH PIPE? match_expr_list END
    { EMatch { subject = $2 ; patterns = $5 } }
  ;

%inline type_expr:
  | PIPE separated_nonempty_list(PIPE, single_variant_type) %prec PIPE (* pipe optional before first variant *)
      { ETypeVariant $2 }
  | separated_nonempty_list(PIPE, single_variant_type) %prec PIPE
      { ETypeVariant $1 }
  | MU l_ident DOT expr %prec prec_mu
    { ETypeMu { var = $2 ; body = $4 } }
  | expr ARROW expr
    { ETypeFun { domain = $1 ; codomain = $3 } }
  ;

single_variant_type:
  | variant_label OF expr
    { { label = $1 ; payload = $3 } }
  ;

appl_expr:
  | appl_expr primary_expr
    { EAppl { func = $1 ; arg = $2 } }
  | variant_label primary_expr
    { EVariant { label = $1 ; payload = $2 } }
  | ASSERT primary_expr
    { EAssert $2 }
  | ASSUME primary_expr
    { EAssume $2 }
  | primary_expr
    { $1 }
  ;

/* In a primary_expr, only primitives, vars, records, and lists do not need
   surrounding parentheses. */
primary_expr:
  | INT
    { EInt $1 }
  | BOOL
    { EBool $1 }
  | ident_usage
    { $1 }
  | INPUT
    { EPick_i }
  | TYPE
    { EType }
  | INT_KEYWORD
    { ETypeInt }
  | BOOL_KEYWORD
    { ETypeBool }
  | UNIT_KEYWORD
    { ETypeUnit }
  // | TOP_KEYWORD
  //   { ETypeTop }
  | BOTTOM_KEYWORD
    { ETypeBottom }
  | LIST
    { EFunction { param = Ident "x" ; body = ETypeList (EVar (Ident "x")) } } (* HACK HACK HACK *)
  // | ABSTRACT
  //   { EAbstractType }
  // | SINGLETYPE_KEYWORD
  //   { ETypeSingle }
  | OPEN_PAREN CLOSE_PAREN
    { EUnit }
  | OPEN_BRACE COLON CLOSE_BRACE
    { ETypeRecord Record.empty }
  | OPEN_BRACE record_body CLOSE_BRACE
    { ERecord $2 }
  | OPEN_BRACE CLOSE_BRACE
    { ERecord Record.empty }
  | OPEN_BRACKET separated_list(SEMICOLON, expr) CLOSE_BRACKET
    { List.fold_right (fun e acc -> 
        EListCons (e, acc)
      ) $2 EEmptyList }
  | OPEN_PAREN expr CLOSE_PAREN
    { $2 }
  // | OPEN_BRACE expr PIPE expr CLOSE_BRACE
  //   { ETypeRefine { tau = $2 ; predicate = $4 } : t }
  // | STRUCT list(statement) END (* may be empty *)
  //   { EModule $2 }
  // | SIG list(val_item) END
  //   { ETypeModule $2 }
  | record_type_or_refinement
    { $1 }
  | primary_expr DOT record_label
    { EProject { record = $1 ; label = $3 } }
  ;

op_expr:
  | expr ASTERISK expr
      { EBinop { left = $1 ; binop = BTimes ; right = $3 } }
  | expr SLASH expr
      { EBinop { left = $1 ; binop = BDivide ; right = $3 } }
  | expr PERCENT expr
      { EBinop { left = $1 ; binop = BModulus ; right = $3 } }
  | expr PLUS expr
      { EBinop { left = $1 ; binop = BPlus ; right = $3 } }
  | expr MINUS expr
      { EBinop { left = $1 ; binop = BMinus ; right = $3 } }
  | expr DOUBLE_COLON expr
      { EListCons ($1, $3) }
  | expr EQUAL_EQUAL expr
      { EBinop { left = $1 ; binop = BEqual ; right = $3 } }
  | expr NOT_EQUAL expr
      { EBinop { left = $1 ; binop = BNeq ; right = $3 } }
  | expr GREATER expr
      { EBinop { left = $1 ; binop = BGreaterThan ; right = $3 } }
  | expr GREATER_EQUAL expr
      { EBinop { left = $1 ; binop = BGeq ; right = $3 } }
  | expr LESS expr
      { EBinop { left = $1 ; binop = BLessThan ; right = $3 } }
  | expr LESS_EQUAL expr
      { EBinop { left = $1 ; binop = BLeq ; right = $3 } }
  | NOT expr
      { ENot $2 }
  | expr DOUBLE_AMPERSAND expr
      { EBinop { left = $1 ; binop = BAnd ; right = $3 } }
  | expr DOUBLE_PIPE expr
      { EBinop { left = $1 ; binop = BOr ; right = $3 } }
  | MINUS INT
      { EInt (-$2) }
  ;

%inline record_type_or_refinement:
  (* exactly one label *)
  | OPEN_BRACE record_type_item CLOSE_BRACE
      { ETypeRecord (Record.Parsing.singleton $2) }
  (* more than one label *)
  | OPEN_BRACE record_type_item SEMICOLON record_type_body CLOSE_BRACE
      { ETypeRecord (Record.Parsing.add_entry $2 $4) }
  (* refinement type with binding for tau, which looks like a record type at first, so that's why we expand the rules above *)
  | OPEN_BRACE l_ident COLON expr PIPE expr CLOSE_BRACE
      { ETypeRefine { var = $2 ; tau = $4 ; predicate = $6 } }
  ;

%inline record_type_item:
  | record_label COLON expr
      { $1, $3 }
  ;

%inline record_expr_item:
  | record_label EQUALS expr
      { $1, $3 }
  ;

record_type_body:
  | record_type_item
      { Record.Parsing.singleton $1 }
  | record_type_item SEMICOLON record_type_body
      { Record.Parsing.add_entry $1 $3 }

%inline record_label:
  | ident
    { Labels.Record.RecordLabel $1 }
  ;

%inline ident_usage:
  | ident
    { EVar $1 }
  ;

%inline l_ident: (* like "lvalue". These are idents that can be assigned to *)
  | ident
    { $1 }
  | UNDERSCORE
    { Ident.Ident "_" }
  ;

%inline ident: (* these are idents that can be used as values *)
  | IDENTIFIER
    { Ident.Ident $1 }
  ;

/* **** Records, lists, and variants **** */

/* e.g. { x = 1 ; y = 2 ; z = 3 } */
record_body:
  | record_expr_item
    { Record.Parsing.singleton $1 }
  | record_expr_item SEMICOLON record_body
    { Record.Parsing.add_entry $1 $3 }
  ;

/* e.g. `Variant 0 */
variant_label:
  | BACKTICK ident
    { Labels.Variant.VariantLabel $2 }
  ;

/* **** Pattern matching **** */

match_expr_list:
  | pattern ARROW expr PIPE match_expr_list
    { ($1, $3) :: $5 }
  | pattern ARROW expr
    { [ $1, $3 ] }

pattern:
  | pattern DOUBLE_COLON pattern
    { PDestructList ($1, $3) }
  | variant_label pattern %prec prec_variant_pattern
    { PVariant { Variant.label = $1 ; payload = $2 } }
  | pattern COMMA pattern
    { PTuple ($1, $3)}
  | OPEN_BRACKET CLOSE_BRACKET 
    { PEmptyList }
  | UNDERSCORE
    { PAny }
  | ident
    { Pattern.PVariable $1 } (* not l_ident because we handle underscore immediately above *)
  | OPEN_PAREN pattern CLOSE_PAREN
    { $2 }
