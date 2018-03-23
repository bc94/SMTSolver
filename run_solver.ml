open Core.Std
open Lexer
open Lexing

let print_pos outx lexbuf = 
    let pos = lexbuf.lex_curr_p in
    fprintf outx "%s:%d:%d" pos.pos_fname
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol +  1)

let parse_with_error lexbuf = 
    try Parser.prog Lexer.read lexbuf with
        | SyntaxError msg -> 
          fprintf stderr "%a: %s\n" print_pos lexbuf msg;
          None
        | Parser.Error ->
          fprintf stderr "%a: syntax error\n" print_pos lexbuf;
          exit (-1)

let rec parse lexbuf = 
    match parse_with_error lexbuf with
        | Some value -> Solver.print_formula value;
                        parse lexbuf
        | None -> ()

let loop filename () =
    let inx = In_channel.create filename in
        let lexbuf = Lexing.from_channel inx in
            lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename};
            parse lexbuf;
            In_channel.close inx

let () =
  Command.basic ~summary:"Parse and print formula"
    Command.Spec.(empty +> anon ("filename" %: file))
    loop 
|> Command.run