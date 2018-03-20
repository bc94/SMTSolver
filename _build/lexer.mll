{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let num = '-'? ['0'-'9'] ['0'-'9']*

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule read =
    parse
    | white             { read lexbuf }
    | newline           { next_line lexbuf; read lexbuf }
    | num               { NUM (int_of_string (Lexing.lexeme lexbuf)) }
    | id                { VAR (Lexing.lexeme lexbuf) }
    | "-<validity>"     { OPEN_VALIDITY }
    | "</validity>"     { CLOSE_VALIDITY }
    | "-<disjunction>"  { OPEN_DISJUNCTION }
    | "</disjunction>"  { CLOSE_DISJUNCTION }
    | "<disjunction/>"  { read lexbuf }
    | "-<conjunction>"  { OPEN_CONJUNCTION }
    | "</conjunction>"  { CLOSE_CONJUNCTION }
    | "<conjunction/>"  { read lexbuf }
    | "-<not>"          { OPEN_NOT }
    | "</not>"          { CLOSE_NOT }
    | "-<atom>"         { OPEN_ATOM }
    | "</atom>"         { CLOSE_ATOM }
    | "-<less>"         { OPEN_LESS }
    | "</less>"         { CLOSE_LESS }   
    | "-<less_equal>"   { OPEN_LESS_EQ }
    | "</less_equal>"   { CLOSE_LESS_EQ }
    | "-<sum>"          { OPEN_SUM }
    | "</sum>"          { CLOSE_SUM }
    | "-<product>"      { OPEN_PRODUCT } 
    | "</product>"      { CLOSE_PRODUCT }
    | "<number>"        { OPEN_NUM }
    | "</number>"       { CLOSE_NUM }
    | "<variable>"      { OPEN_VAR }
    | "</variable>"     { CLOSE_VAR }
    | eof               { EOF }
