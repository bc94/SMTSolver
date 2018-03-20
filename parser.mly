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
    | OPEN_VALIDITY; e = elem_list; CLOSE_VALIDITY   { Formula e }
    ;

elem_list:
    | OPEN_CONJUNCTION; el = elem_list; CLOSE_CONJUNCTION  { Conjunction el }
    | OPEN_DISJUNCTION; el = elem_list; CLOSE_DISJUNCTION  { Disjunction el }
    | OPEN_NOT; el = elem_list; CLOSE_NOT  { Not el }
    | l = literal; el = elem_list   { e :: el }
    | (* empty *)   { [] }
    ;

literal:
    | OPEN_NOT; l = literal; CLOSE_NOT  { Not l }
    | OPEN_ATOM; c = comparator; CLOSE_ATOM { Atom (Constraint c) }
    ;

comparator:
    | OPEN_LESS; np = num_pair_l; CLOSE_LESS  { (id_count, LessEq np); let id_count = id_count + 1 }
    | OPEN_LESS_EQ; np = num_pair_le; CLOSE_LESS_EQ    { (id_count, LessEq np); let id_count = id_count + 1 }
    ;

num_pair_l:
    | n1 = num; n2 = num_l    { (n1, n2) }
    ;

num_pair_le:
    | n1 = num; n2 = num    { (n1, n2) }
    ;

num:
    | s = sum   { s }
    | p = product   { p }
    | n = number    { n }
    | v = var   { v }
    ;

num_l:
    | n = NUM   { n - 1 }

sum:
    | OPEN_SUM; n1 = num; n2 = num; CLOSE_SUM   { Sum (n1, n2) }
    ;

product:
    | OPEN_PRODUCT; n1 = num; n2 = num; CLOSE_PRODUCT   { Prod (n1, n2) }
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

open Types
open Tokens

let id_count = 0;;