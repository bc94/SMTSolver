%token OPEN_VALIDITY
%token CLOSE_VALIDITY
%token OPEN_DISJUNCTION
%token CLOSE_DISJUNCTION
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

%start <inequalities option> prog
%%

prog:
    | EOF   { None }
    | i = inequalities   { Some i }
    ;

formula:
    | OPEN_VALIDITY; d = disj; CLOSE_VALIDITY   { Ineq d }
    ;

disj:
    | OPEN_DISJUNCTION; cs = constraints; CLOSE_DISJUNCTION  { cs }
    ;

constraints:
    | n = not; cs = constraints  { n :: cs }
    | n = not   { n }
    ;

not:
    | OPEN_NOT; a = atom; CLOSE_NOT { Not a }
    ;

atom:
    | OPEN_ATOM; c = comparator; CLOSE_ATOM { Constraint c }
    ;

comparator:
    | OPEN_LESS; np = num_pair; CLOSE_LESS  { (id_count, Less np); let id_count = id_count + 1 }
    | OPEN_LESS_EQ; np = num_pair; CLOSE_LESS_EQ    { (id_count, LessEq np); let id_count = id_count + 1 }
    ;

num_pair:
    | n1 = num; n2 = num    { (n1, n2) }
    ;

num:
    | s = sum   { Fun s }
    | p = product   { Fun p }
    | n = number    { n }
    | v = var   { v }
    ;

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

let id_count = 0;;