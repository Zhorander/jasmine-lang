

(* values *)
%token <string> IDENT STRING
%token <int> INT

%token TRUE
%token FALSE

%token FUN
(* keywords *)
%token WHILE




%token ELSE
%token IF
%token RETURN
%token LET
(* groupings *)
%token LEFT_PAREN
%token RIGHT_PAREN


%token LEFT_BRACE
%token RIGHT_BRACE
(* types *)
%token T_INT
%token T_BOOL
(* symbols *)
%token COLON
%token COMMA
%token MINUS
%token PLUS
%token SLASH
%token STAR
%token BANG
%token BANG_EQUAL
%token EQUAL
%token EQUAL_EQUAL




(* misc *)
%token EOF
%token SEMICOLON


// %left AND_AND OR_OR
%left EQUAL_EQUAL (* BANG_EQUAL GREATER GREATER_EQUAL LESS LESS_EQUAL *)
%left PLUS MINUS
%left STAR SLASH
%nonassoc (* UMINUS *) BANG

%start <Syntax.Untyped.stmt list option> prog
%%

prog:
  | t = toplevel_declaration+ EOF { Some t }
  | EOF                       { None }
  ;

toplevel_declaration:
  | f = function_definition   { f }
  | d = declaration_statement { d }
  ;

(* Function Definition *)
function_definition:
  | FUN n = IDENT p = param_type_list COLON t = signature? body = compound_statement
    { Syntax.Untyped.Fun_def { name=n;params=p;ret_t=t; body=body } }
  ;

param_type_list:
  | LEFT_PAREN args = separated_list(COMMA, arg_dec) RIGHT_PAREN { args }
  ;

arg_dec: n = IDENT COLON t = signature { (n, t) }
  ;

(* Signature Definition *)
(* ----------------------------------------------- *)


signature:
  | t = type_specifier { t }
  ;

type_specifier:
  | T_INT  { Types.T_int }
  | T_BOOL { Types.T_bool }
  ;
(* ----------------------------------------------- *)

(* Expressions *)
(* ----------------------------------------------- *)
expr:
  | ce = const_expr                      { ce }
  | n = IDENT LEFT_PAREN a = separated_list(COMMA, expr) RIGHT_PAREN
    { Syntax.Untyped.Funcall (n, a) }
  | b = bin_expr                         { b }
  | LEFT_PAREN e = expr RIGHT_PAREN      { Syntax.Untyped.Group e }
  // | uop = unop r = expr %prec UMINUS  { Jasmine.Exp.Unary (uop,r) }
  | u = un_expr                          { u }
  ;

const_expr:
  | id = IDENT                       { Syntax.Untyped.Ident id }
  | i = INT                          { Syntax.Untyped.Int i }
  | TRUE                             { Syntax.Untyped.Bool true }
  | FALSE                            { Syntax.Untyped.Bool false }
  ;

un_expr:
  | BANG e = expr  { Syntax.Untyped.Not e }
  // | MINUS { Jasmine.Operator.Minus }
  ;




bin_expr:
  | lhe = expr EQUAL_EQUAL rhe = expr { Syntax.Untyped.Equal (lhe, rhe) }
  | lhe = expr BANG_EQUAL rhe = expr  { Syntax.Untyped.Not_equal (lhe, rhe) }
  | lhe = expr PLUS rhe = expr        { Syntax.Untyped.Plus (lhe, rhe) }
  | lhe = expr MINUS rhe = expr       { Syntax.Untyped.Sub (lhe, rhe) }
  | lhe = expr STAR rhe = expr        { Syntax.Untyped.Mult (lhe, rhe) }
  | lhe = expr SLASH rhe = expr       { Syntax.Untyped.Div (lhe, rhe) }
  ;
(* ----------------------------------------------- *)

(* Statements *)
(* ----------------------------------------------- *)
statement:
  | e = expression_statement  { e }
  | d = declaration_statement { d }
  | it = iteration_statement  { it }
  | s = selection_statement   { s }
  | c = compound_statement    { c }
  | a = assignment_statement  { a }
  | j = jump_statement        { j }
  ;

declaration_statement:
  | LET id = IDENT COLON t = signature EQUAL e = expr SEMICOLON
    { Syntax.Untyped.Vardec (id, t, e) }
  (* struct and enum declaration go here *)
  ;

compound_statement:
  LEFT_BRACE s = list(statement) RIGHT_BRACE { Syntax.Untyped.Compound s }
  ;

expression_statement: e = expr SEMICOLON { Syntax.Untyped.Exp e };

selection_statement:
  | IF e = expr s = statement
    { Syntax.Untyped.If (e, s, None) }
  | IF e = expr s = statement ELSE els = statement
    { Syntax.Untyped.If (e, s, (Some els)) }
  ;

iteration_statement:
  | WHILE cond = expr cs = statement
    { Syntax.Untyped.While (cond, cs) }
  ;

assignment_statement: lhe = expr EQUAL rhe = expr SEMICOLON
  { Syntax.Untyped.Mutate (lhe, rhe) }
  ;

jump_statement:
  | RETURN e = expr { Syntax.Untyped.Return e }
  ;
(* ----------------------------------------------- *)
