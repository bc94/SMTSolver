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
%token OPEN_PAR
%token CLOSE_PAR
%token ASSERT
%token AND 
%token OR 
%token NOT
%token LET
%token EQ
%token LT
%token GT
%token LEQ
%token GEQ
%token PLUS
%token MINUS
%token TIMES
%token DIVIDED
%token <int> NUM 
%token <string> VAR
%token EOF

%start <Types.subst_list option> prog
%%

prog:
    | f = formula  { Some f }
    | EOF   { None }
    ;

formula:
    | OPEN_VALIDITY; e = elem; CLOSE_VALIDITY   { SubstList ([SubstForm (Formula (Not e))]) }
    | OPEN_PAR; ASSERT; e = elem_smt2; CLOSE_PAR    { SubstList ([SubstForm (Formula e)]) }
    | OPEN_PAR; ASSERT; OPEN_PAR; LET; OPEN_PAR; ll = let_list_smt2; CLOSE_PAR; l = let_smt2; CLOSE_PAR; CLOSE_PAR { SubstList (ll @ l) }
    ;

elem_smt2:
    | OPEN_PAR; AND; el = elem_list_smt2; CLOSE_PAR  { Conjunction el }
    | OPEN_PAR; OR; el = elem_list_smt2; CLOSE_PAR   { Disjunction el }
    | OPEN_PAR; NOT; e = elem_smt2; CLOSE_PAR    { Not e }
    | OPEN_PAR; l = literal_smt2; CLOSE_PAR  { l }
    | l = literal_smt2  { l }
    ;

let_list_smt2:
    | OPEN_PAR; n = num_smt2; e = elem_smt2; CLOSE_PAR; ll = let_list_smt2  { [SubstElem (n, e)] @ ll }
    | OPEN_PAR; n = num_smt2; l = literal_smt2; CLOSE_PAR; ll = let_list_smt2  { [SubstElem (n, l)] @ ll }
    | OPEN_PAR; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR; ll = let_list_smt2 { [SubstNum (n1, n2)] @ ll }
    | (* empty *)   { [] }
    ;

let_smt2:
    | OPEN_PAR; LET; OPEN_PAR; ll = let_list_smt2; CLOSE_PAR; l = let_smt2; CLOSE_PAR   { ll @ l }
    | e = elem_smt2 { [SubstForm (Formula e)] }
    ;

elem_list_smt2:
    | e = elem_smt2; el = elem_list_smt2    { e :: el }
    | (* empty *)   { [] }
    ;

literal_smt2:
    | EQ; n1 = num_smt2; n2 = num_smt2  { Conjunction ([(Atom (Constraint (LessEq (n1, n2))))] @ [(Atom (Constraint (LessEq (n2, n1))))]) }
    | EQ; OPEN_PAR; n1 = num_smt2; CLOSE_PAR; n2 = num_smt2 { Conjunction ([(Atom (Constraint (LessEq (n1, n2))))] @ [(Atom (Constraint (LessEq (n2, n1))))]) }
    | LT; n1 = num_smt2; n2 = num_smt2  { Atom (Constraint (Less (n1, n2))) }
    | GT; n1 = num_smt2; n2 = num_smt2  { Atom (Constraint (Less (n2, n1))) }
    | LEQ; n1 = num_smt2; n2 = num_smt2 { Atom (Constraint (LessEq (n1, n2))) }
    | GEQ; n1 = num_smt2; n2 = num_smt2 { Atom (Constraint (LessEq (n2, n1))) }
    | v = VAR   { Atom (RVar (v)) }
    ;

num_smt2:
    | OPEN_PAR; PLUS; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR   { Sum ([n1; n2]) } 
    | OPEN_PAR; MINUS; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR  { Sum ([n1; (Prod ([(Num (-1)); n2]))]) }
    | OPEN_PAR; TIMES; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR  { Prod ([n1; n2]) }
    | OPEN_PAR; DIVIDED; n1 = number_smt2; n2 = number_smt2; CLOSE_PAR    { Div (n1, n2) }
    | v = var_smt2  { v }
    ;

num_l_smt2:
    | OPEN_PAR; PLUS; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR   { Sum ([n1; n2; (Num (-1))]) } 
    | OPEN_PAR; MINUS; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR  { Sum ([n1; (Prod ([(Num (-1)); n2])); (Num (-1))]) }
    | OPEN_PAR; TIMES; n1 = num_smt2; n2 = num_smt2; CLOSE_PAR  { Sum ([(Prod ([n1; n2])); (Num (-1))]) }
    | OPEN_PAR; DIVIDED; n1 = NUM; n2 = NUM; CLOSE_PAR    { Div (Num (n1 - n2), Num (n2)) }
    | OPEN_PAR; DIVIDED; OPEN_PAR; MINUS; n1 = NUM; CLOSE_PAR; n2 = NUM CLOSE_PAR    { Div (Num ((-1) * (n1 - n2)), Num (n2)) }
    | v = var_smt2  { Sum ([v; (Num (-1))]) }
    ;

number_smt2:
    | OPEN_PAR; MINUS; n = NUM; CLOSE_PAR   { Num ((-1) * n) }
    | n = NUM  { Num (n) }
    ;

var_smt2:
    | OPEN_PAR; MINUS; n = NUM; CLOSE_PAR   { Num ((-1) * n) }
    | n = NUM  { Num (n) }
    | v = VAR  { Var (v) }
    ;

elem:
    | OPEN_CONJUNCTION; el = elem_list; CLOSE_CONJUNCTION  { Conjunction el }
    | OPEN_DISJUNCTION; el = elem_list; CLOSE_DISJUNCTION  { Disjunction el }
    | OPEN_NOT; e = elem; CLOSE_NOT  { Not e }
    | TRUE  { Atom (Constraint (LessEq ((Num 0), (Num 1)))) }
    | FALSE { Atom (Constraint (LessEq ((Num 1), (Num 0)))) }
    | l = literal   { l }
    ;

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
    | n1 = num; n2 = num    { Less (n1, n2) }
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