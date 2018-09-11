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

let rec parse lexbuf option = 
    match parse_with_error lexbuf with
        | Some value -> (
                         match option with
                            | "indexed" -> let (f, cs, i_map, inv_map) = (Util.time Tseitin.tseitin_transformation_inc_i value) in
                                                Util.time Solver.sat_inc_i (f, cs, i_map, inv_map)
                            | "incremental" -> let (f, cs, i_map, inv_map) = (Util.time Tseitin.tseitin_transformation_inc value) in
                                                Util.time Solver.sat_inc (f, cs, i_map, inv_map)
                            | "twl" -> Util.time Solver.sat_twl (Util.time Tseitin.tseitin_transformation value)
                            | "simple" -> Util.time Solver.sat (Util.time Tseitin.tseitin_transformation value)
                            | _ -> failwith "Unknown command line option"
                        (*printf "Before Tseitin: \n\n";
                        Solver.print_formula value;
                        printf "\n\nAfter Tseitin \n\n";
                        Solver.print_formula (Solver.tseitin_transformation value);*)
                        ); parse lexbuf option
        | None -> ()

let loop filename option () =
    let inx = In_channel.create filename in
        let lexbuf = Lexing.from_channel inx in
            lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename};
            parse lexbuf option;
            In_channel.close inx

let () =
  Command.basic ~summary:"Parse and print formula"
    Command.Spec.(empty +> anon ("filename" %: file) +> anon ("option" %: string))
    loop 
|> Command.run