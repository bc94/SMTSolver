
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | OPEN_VAR
  | OPEN_VALIDITY
  | OPEN_SUM
  | OPEN_PRODUCT
  | OPEN_NUM
  | OPEN_NOT
  | OPEN_LESS_EQ
  | OPEN_LESS
  | OPEN_DISJUNCTION
  | OPEN_CONJUNCTION
  | OPEN_ATOM
  | NUM of (int)
  | EOF
  | CLOSE_VAR
  | CLOSE_VALIDITY
  | CLOSE_SUM
  | CLOSE_PRODUCT
  | CLOSE_NUM
  | CLOSE_NOT
  | CLOSE_LESS_EQ
  | CLOSE_LESS
  | CLOSE_DISJUNCTION
  | CLOSE_CONJUNCTION
  | CLOSE_ATOM

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Types.formula option)
