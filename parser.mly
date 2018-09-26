%{
    
open Types

%}

%token OPEN_VALIDITY
%token CLOSE_VALIDITY
%token OPEN_DISJUNCTION
%token CLOSE_DISJUNCTION
%token OPEN_CONJUNCTION
%token CLOSE_CONJUNCTION
%token TRUE
%token FALSE
%token OPEN_NOT
%token CLOSE_NOT
%token OPEN_ATOM
%token CLOSE_ATOM
%token OPEN_LESS
%token CLOSE_LESS
%token OPEN_LESS_EQ
%token CLOSE_LESS_EQ
%token OPEN_EQ
%token CLOSE_EQ 
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
    | OPEN_VALIDITY; e = elem; CLOSE_VALIDITY   { Formula (Not e) }
    ;

elem:
    | OPEN_CONJUNCTION; el = elem_list; CLOSE_CONJUNCTION  { Conjunction el }
    | OPEN_DISJUNCTION; el = elem_list; CLOSE_DISJUNCTION  { Disjunction el }
    | OPEN_NOT; e = elem; CLOSE_NOT  { Not e }
    | TRUE  { Atom (Constraint (LessEq ((Num 0), (Num 1)))) }
    | FALSE { Atom (Constraint (LessEq ((Num 1), (Num 0)))) }
    | l = literal   { l }

elem_list:
    | e = elem; el = elem_list   { e :: el }
    | (* empty *)   { [] }
    ;

literal:
    | OPEN_NOT; l = literal; CLOSE_NOT  { Not l }
    | OPEN_ATOM; OPEN_EQ; n1 = num; n2 = num; CLOSE_EQ; CLOSE_ATOM  { Conjunction ([(Atom (Constraint (LessEq (n1, n2))))] @ [(Atom (Constraint (LessEq (n2, n1))))]) }
    | OPEN_ATOM; c = constr; CLOSE_ATOM { Atom  c }
    ;

constr:
    | OPEN_LESS; np = num_pair_l; CLOSE_LESS  { Constraint np }
    | OPEN_LESS_EQ; np = num_pair_le; CLOSE_LESS_EQ    { Constraint np }
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
    | s = sum_l { s }
    | p = product_l { p }
    | n = number_l { n }
    | v = var   { Sum ([v] @ [Num (-1)]) }
    ;

num_list:
    | n = num; nl = num_list    { n :: nl }
    | (* empty *)   { [] }
    ;

sum:
    | OPEN_SUM; nl = num_list; CLOSE_SUM   { Sum (nl) }
    ;

sum_l:
    | OPEN_SUM; nl = num_list; CLOSE_SUM  { Sum (nl @ [(Num (-1))]) }
    ;

product:
    | OPEN_PRODUCT; nl = num_list; CLOSE_PRODUCT   { Prod (nl) }
    ;

product_l:
    | OPEN_PRODUCT; nl = num_list; CLOSE_PRODUCT    { Sum ([Prod (nl)] @ [(Num (-1))]) }
    ;

number:
    | OPEN_NUM; c = constant; CLOSE_NUM { Num c }
    ;

number_l:
    | OPEN_NUM; c = constant; CLOSE_NUM  { Num (c - 1) }

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