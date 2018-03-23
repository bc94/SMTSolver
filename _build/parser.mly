%{
    
open Types

%}

%token OPEN_VALIDITY
%token CLOSE_VALIDITY
%token OPEN_DISJUNCTION
%token CLOSE_DISJUNCTION
%token OPEN_CONJUNCTION
%token CLOSE_CONJUNCTION
%token OPEN_NOT
%token CLOSE_NOT
%token OPEN_ATOM
%token CLOSE_ATOM
%token OPEN_LESS
%token CLOSE_LESS
%token OPEN_LESS_EQ
%token CLOSE_LESS_EQ
%token OPEN_SUM
%token CLOSE_SUM
%token OPEN_PRODUCT
%token CLOSE_PRODUCT
%token OPEN_NUM
%token CLOSE_NUM
%token OPEN_VAR
%token CLOSE_VAR
%token <int> NUM 
%token <string> VAR
%token EOF

%start <Types.formula option> prog
%%

prog:
    | f = formula  { Some f }
    | EOF   { None }
    ;

formula:
    | OPEN_VALIDITY; e = elem; CLOSE_VALIDITY   { Formula e }
    ;

elem:
    | OPEN_CONJUNCTION; el = elem_list; CLOSE_CONJUNCTION  { Conjunction el }
    | OPEN_DISJUNCTION; el = elem_list; CLOSE_DISJUNCTION  { Disjunction el }
    | OPEN_NOT; e = elem; CLOSE_NOT  { Not e }
    | l = literal   { l }

elem_list:
    | e = elem; el = elem_list   { e :: el }
    | (* empty *)   { [] }
    ;

literal:
    | OPEN_NOT; l = literal; CLOSE_NOT  { Not l }
    | OPEN_ATOM; c = constr; CLOSE_ATOM { Atom  c }
    ;

constr:
    | OPEN_LESS; np = num_pair_l; CLOSE_LESS  { Constraint (0, np) }
    | OPEN_LESS_EQ; np = num_pair_le; CLOSE_LESS_EQ    { Constraint (0, np) }
    ;

num_pair_l:
    | n1 = num; n2 = num_l    { LessEq (n1, n2) }
    ;

num_pair_le:
    | n1 = num; n2 = num    { LessEq (n1, n2) }
    ;

num:
    | s = sum   { s }
    | p = product   { p }
    | n = number    { n }
    | v = var   { v }
    ;

num_l:
    | n = NUM   { Num (n - 1) }

num_list:
    | n = num; nl = num_list    { n :: nl }
    | (* empty *)   { [] }

sum:
    | OPEN_SUM; nl = num_list; CLOSE_SUM   { Sum (nl) }
    ;

product:
    | OPEN_PRODUCT; nl = num_list; CLOSE_PRODUCT   { Prod (nl) }
    ;

number:
    | OPEN_NUM; c = constant; CLOSE_NUM { Num c }
    ;

var:
    | OPEN_VAR; v = variable; CLOSE_VAR { Var v }
    ;

constant:
    | n = NUM   { n }
    ;

variable:
    | v = VAR   { v }
    ;

%%