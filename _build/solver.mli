type token = OPEN_VALIDITY
           | CLOSE_VALIDITY
           | OPEN_DISJUNCTION
           | CLOSE_DISJUNCTION
           | OPEN_CONJUNCTION
           | CLOSE_CONJUNCTION
           | OPEN_NOT
           | CLOSE_NOT
           | OPEN_ATOM
           | CLOSE_ATOM
           | OPEN_LESS
           | CLOSE_LESS
           | OPEN_LESS_EQ
           | CLOSE_LESS_EQ
           | OPEN_SUM
           | CLOSE_SUM
           | OPEN_PRODUCT
           | CLOSE_PRODUCT
           | OPEN_NUM
           | CLOSE_NUM
           | OPEN_VAR
           | CLOSE_VAR
           | NUM 
           | VAR
           | EOF;;

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Types.formula option