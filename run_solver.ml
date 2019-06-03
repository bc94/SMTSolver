open Core.Std
open Lexer
open Lexing
open Types
open List
open Simplex_Validity_Checker

(*let transform_and_run_list formula = 
        let (f, cs, i_map, inv_map, _) = (Tseitin.tseitin_transformation_inc_i formula) in
           Solver.sat_inc_i_list (f, cs, i_map, inv_map);;*)

(*let transform_substitute_and_run_list (subst_form_pair : 'a * 'b) = 
        let (f, cs, i_map, inv_map, _) = (Tseitin.tseitin_transformation_inc_i (Util.variable_substitution subst_form_pair)) in
           Solver.sat_inc_i_list (f, cs, i_map, inv_map);;*)

let transform_and_run_indexed formula = 
        let (f, cs, i_map, inv_map, vsids) = (Tseitin.tseitin_transformation_inc_i formula) in
           Solver.sat_inc_i (f, cs, i_map, inv_map, vsids);;

let transform_substitute_and_run_indexed (subst_form_pair : 'a * 'b) = 
        let (f, cs, i_map, inv_map, vsids) = (Tseitin.tseitin_transformation_inc_i (Util.variable_substitution subst_form_pair)) in
           Solver.sat_inc_i (f, cs, i_map, inv_map, vsids);;

let transform_and_run_ceta formula = 
        let Formula (form) = formula in
        let f = Util.to_ceta_format (Formula (Not (form))) in 
        match (Simplex_Validity_Checker.check_well_formed_RA_formula_string_vars f) with
                | true -> ( 
                           match (Simplex_Validity_Checker.check_valid_RA_formula_string_vars f) with
                                | Simplex_Validity_Checker.Inl (_) -> Printf.printf "NOT VALID "
                                | Simplex_Validity_Checker.Inr (_) -> Printf.printf "VALID "
                          )
                | false -> failwith "[Invalid argument] formula not well formed with respect to the Simplex_Validity_Checker module";;

let transform_substitute_and_run_ceta (subst_form_pair : 'a * 'b) = 
        let (xs, Formula (form)) = subst_form_pair in 
        let f = Util.to_ceta_format (Util.variable_substitution (xs, Formula (Not (form)))) in 
        match (Simplex_Validity_Checker.check_well_formed_RA_formula_string_vars f) with
                | true -> ( 
                           match (Simplex_Validity_Checker.check_valid_RA_formula_string_vars f) with
                                | Simplex_Validity_Checker.Inl (_) -> Printf.printf "NOT VALID "
                                | Simplex_Validity_Checker.Inr (_) -> Printf.printf "VALID "
                          )
                | false -> failwith "[Invalid argument] formula not well formed with respect to the Simplex_Validity_Checker module";;

(*let run_solver_list (value : subst_list) = 
    match value with 
        | SubstList (x :: xs) -> (
                                match length (x :: xs) with
                                        | 1 -> (
                                                match (hd (x :: xs)) with 
                                                 | Some (SubstForm (formula)) -> Util.time transform_and_run_list formula;
                                                                                 (*Util.time transform_and_run_ceta formula*)
                                                 | _ -> failwith "Result of parsing not a formula"
                                               )
                                        | _ -> (
                                                match (hd (rev (x :: xs))) with 
                                                 | Some (SubstForm (formula)) -> Util.time transform_substitute_and_run_list ((tl (rev (x :: xs))), formula);
                                                                                 (*Util.time transform_substitute_and_run_ceta ((tl (rev (x :: xs))), formula)*)
                                                 | _ -> failwith "Result of parsing not a formula"
                                               )
                                )
        | SubstList ([]) -> failwith "Parsed formula empty";;*)

let run_solver_indexed (value : subst_list) = 
    match value with 
        | SubstList (x :: xs) -> (
                                match length (x :: xs) with
                                        | 1 -> (
                                                match (hd (x :: xs)) with 
                                                 | Some (SubstForm (formula)) -> Util.time transform_and_run_indexed formula;
                                                                                 (*Util.time transform_and_run_ceta formula*)
                                                 | _ -> failwith "Result of parsing not a formula"
                                               )
                                        | _ -> (
                                                match (hd (rev (x :: xs))) with 
                                                 | Some (SubstForm (formula)) -> Util.time transform_substitute_and_run_indexed ((tl (rev (x :: xs))), formula);
                                                                                 (*Util.time transform_substitute_and_run_ceta ((tl (rev (x :: xs))), formula)*)
                                                 | _ -> failwith "Result of parsing not a formula"
                                               )
                                )
        | SubstList ([]) -> failwith "Parsed formula empty";;
    
let run_solver_incremental value = 
    match value with 
        | SubstList (x :: xs) -> (
                                match length (x :: xs) with
                                        | 1 -> (
                                                match (hd (x :: xs)) with 
                                                | Some (SubstForm (formula)) -> let (f, cs, i_map, inv_map) = (Tseitin.tseitin_transformation_inc formula) in
                                                                                Solver.sat_inc (f, cs, i_map, inv_map)
                                                | _ -> failwith "Result of parsing not a formula"
                                                )
                                        | _ -> (
                                                match (hd (rev (x :: xs))) with 
                                                | Some (SubstForm (formula)) -> let (f, cs, i_map, inv_map) = (Tseitin.tseitin_transformation_inc (Util.variable_substitution (tl (rev (x :: xs)), formula))) in
                                                                                Solver.sat_inc (f, cs, i_map, inv_map)
                                                | _ -> failwith "Result of parsing not a formula"
                                                )
                                )
        | SubstList([]) -> failwith "Parsed formula empty";;

let run_solver_twl value = 
    match value with 
        | SubstList (x :: xs) -> (
                                match length (x :: xs) with
                                        | 1 -> (
                                                match (hd (x :: xs)) with 
                                                | Some (SubstForm (formula)) -> Solver.sat_twl (Tseitin.tseitin_transformation formula)
                                                | _ -> failwith "Result of parsing not a formula"
                                               )
                                        | _ -> (
                                                match (hd (rev (x :: xs))) with 
                                                | Some (SubstForm (formula)) -> Solver.sat_twl (Tseitin.tseitin_transformation (Util.variable_substitution (tl (rev (x :: xs)), formula)))
                                                | _ -> failwith "Result of parsing not a formula"
                                               )
                                )
        | SubstList ([]) -> failwith "Parsed formula empty";;

let run_solver_simple value = 
    match value with 
        | SubstList (x :: xs) -> (
                                match length (x :: xs) with
                                        | 1 -> (
                                                match (hd (x :: xs)) with 
                                                | Some (SubstForm (formula)) -> Solver.sat (Tseitin.tseitin_transformation formula)
                                                | _ -> failwith "Result of parsing not a formula"
                                               )
                                        | _ -> (
                                                match (hd (rev (x :: xs))) with 
                                                | Some (SubstForm (formula)) -> Solver.sat (Tseitin.tseitin_transformation (Util.variable_substitution (tl (rev (x :: xs)), formula)))
                                                | _ -> failwith "Result of parsing not a formula"
                                               )
                                )
        | SubstList ([]) -> failwith "Parsed formula empty";;

let print_pos outx lexbuf = 
    let pos = lexbuf.lex_curr_p in
    fprintf outx "%s:%d:%d" pos.pos_fname
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol +  1)

let parse_with_error lexbuf : subst_list option = 
    try Parser.prog Lexer.read lexbuf with
        | SyntaxError msg -> 
          fprintf stderr "%a: %s\n" print_pos lexbuf msg;
          None
        | Parser.Error -> 
          printf "%s\n" (Lexing.lexeme lexbuf);
          fprintf stderr "%a: syntax error\n" print_pos lexbuf;
          exit (-1)

let rec parse lexbuf opt = 
   match parse_with_error lexbuf with
        | Some (value) -> (
                         match opt with
                            (*| "list" -> run_solver_list value*)
                            | "indexed" -> run_solver_indexed value 
                            | "incremental" -> Util.time run_solver_incremental value
                            | "twl" -> Util.time run_solver_twl value
                            | "simple" -> Util.time run_solver_simple value
                            | _ -> failwith "Unknown command line option"
                        ); 
                        parse lexbuf opt
        | None -> ()

let loop filename opt () =
    let inx = In_channel.create filename in
        let lexbuf = Lexing.from_channel inx in
            lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename};
            parse lexbuf opt;
            In_channel.close inx

let () =
  Command.basic ~summary:"Parse and print formula"
    Command.Spec.(empty +> anon ("filename" %: file) +> anon ("option" %: string))
    loop 
|> Command.run