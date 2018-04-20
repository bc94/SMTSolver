open String
open Types
open List
open Core.Std

(* Profiling *)

let time f x =
    let start = Unix.gettimeofday ()
    in let res = f x
    in let stop = Unix.gettimeofday ()
    in let () = Printf.printf "Time: %fs\n%!" (stop -. start)
    in
       res;;

(* Functions for printing a formula *)

let rec print_num_type_list nl = 
    match nl with
        | [] -> "[]"
        | x :: xs -> (print_num_type x) ^ ", " ^ (print_num_type_list xs)

and print_num_type n = 
    match n with
        | Sum (xs) -> "Sum ([" ^ (print_num_type_list xs) ^ "])" 
        | Prod (xs) -> "Prod ([" ^ (print_num_type_list xs) ^ "])"
        | Num (x) -> "Num " ^ (string_of_int x)
        | Var (x) -> "Var " ^ x
        | _ -> failwith "[Invalid formula]: print_num_type"

let print_less_equal le =
    match le with
        | LessEq (x, y) -> "LessEq (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")"
        | _ -> failwith "[Invalid formula]: print_less_equal"

let print_constraint_n c = 
    match c with
        | Constraint (x) ->  "Constraint (" ^ (print_less_equal x) ^ ")"  
        | AuxVar (x) -> "AuxVar (" ^ (string_of_int x) ^ ")"      
        | _ -> failwith "[Invalid formula]: print_constraint_n"

let rec print_element_list el = 
    match el with
        | [] -> "[]"
        | x :: xs -> (print_element x) ^ ", " ^ (print_element_list xs)

and print_element e =
    match e with 
        | Not (x) -> "Not (" ^ (print_element x) ^ ")"
        | Conjunction (x) -> "Conjunction ([" ^ (print_element_list x) ^ "])"
        | Disjunction (x) -> "Disjunction ([" ^ (print_element_list x) ^ "])"
        | Atom (x) -> "Atom (" ^ (print_constraint_n x) ^ ")"
        | _ -> failwith "[Invalid formula]: print_element"

let print_formula f = 
    match f with
        | Formula (x) -> printf "Formula (%s)\n" (print_element x)
        | _ -> failwith "[Invalid formula]"

let rec print_assignment_rec assignment =
    match assignment with 
        | Assignment ([]) -> ""
        | Assignment ((y, b, d, dl) :: xs) -> "(" ^ (print_constraint_n y) ^ ", " ^ (string_of_bool b) ^ ", " ^ (string_of_bool d) ^ ", " ^ (string_of_int dl) ^ "); " ^ (print_assignment_rec (Assignment (xs)));;

let print_assignment assignment = printf "Assignment (%s)\n" (print_assignment_rec assignment);;

(* Utilities for DPLL *)

let rec is_assigned (assignment : assignment) (literal : element) =
    match assignment with
        | Assignment ([]) -> false
        | Assignment (x :: xs) -> (
                                   match (x, literal) with 
                                    | ((y, b, d, dl), Atom (z)) -> ( 
                                                                    match (compare y z) with 
                                                                    | 0 -> true
                                                                    | _ -> is_assigned (Assignment xs) literal
                                                                   )
                                    | ((y, b, d, dl), Not (Atom (z))) -> (
                                                                          match (compare y z) with 
                                                                            | 0 -> true
                                                                            | _ -> is_assigned (Assignment xs) literal
                                                                         )
                                    | _ -> failwith "[Invalid argument] is_assigned: second argument is not a literal"
                                  )
        | _ -> failwith "[Invalid argument] first argument is not a constraint_n * bool list";;

let rec is_true (assignment : assignment) (literal : element) = 
    match assignment with
        | Assignment ([]) -> false
        | Assignment (x :: xs) -> (
                                   match (x, literal) with 
                                    | ((y, true, d, dl), Atom (z)) -> ( 
                                                                       match (compare y z) with 
                                                                        | 0 -> true
                                                                        | _ -> is_true (Assignment xs) literal
                                                                      )
                                    | ((y, true, d, dl), Not (Atom (z))) -> is_true (Assignment xs) literal
                                    | ((y, false, d, dl), Not (Atom (z))) -> (
                                                                              match (compare y z) with 
                                                                                | 0 -> true
                                                                                | _ -> is_true (Assignment xs) literal
                                                                             )   
                                    | ((y, false, d, dl), Atom(z)) -> is_true (Assignment xs) literal
                                    | _ -> failwith "[Invalid argument] is_true: second argument not a literal"
                                  )
        | _ -> failwith "[Invalid argument] first argument is not a constraint_n * bool list";;        

let rec is_clause_satisfied assignment clause =
    match clause with 
        | Disjunction ([]) -> false
        | Disjunction (x :: xs) -> (
                                    match (is_true assignment x) with
                                    | true -> true
                                    | false -> is_clause_satisfied assignment (Disjunction (xs))
                                   )
        | Atom (x) -> (
                       match (is_true assignment clause) with
                        | true -> true
                        | false -> false
                      )
        | Not (Atom (x)) -> (
                             match (is_true assignment clause) with
                                | true -> true
                                | false -> false
                            )
        | _ -> failwith "[Invalid argument] second argument is not a Disjunction of element list";;

(* Checking unassigned for single literal cases is not necessary since unit is always *)
(* applied before ever calling this function, assigning values to all unit clauses  *)
let rec unassigned_or_true_l assignment clause ls =
    match clause with
        | Atom (x) -> (
                       match (is_true assignment (Atom (x))) with
                        | true -> [Atom (x)]
                        | false -> []
                      )
        | Not (Atom (x)) -> (
                             match (is_true assignment (Not (Atom (x)))) with
                                | true -> [Not (Atom (x))]
                                | false -> []
                            )
        | Disjunction ([]) -> ls
        | Disjunction (x :: xs) -> (
                                    match (is_true assignment x) with
                                    | true -> unassigned_or_true_l assignment (Disjunction (xs)) (ls @ [x])
                                    | false -> (
                                                match (is_assigned assignment x) with 
                                                    | true -> unassigned_or_true_l assignment (Disjunction (xs)) ls
                                                    | false -> unassigned_or_true_l assignment (Disjunction (xs)) (ls @ [x])
                                               )
                                    | _ -> failwith "[Invalid argument] unassigned_or_true_l"
                                  )
        | _ -> failwith "[Invalid argument] unassigned_or_true_l";;

let unassigned_or_true assignment clause = unassigned_or_true_l assignment clause [];;

let unit_propagation_applicable assignment clause =
    match (unassigned_or_true assignment clause) with
        | [] -> []
        | xs -> (
                 match (length xs, is_assigned assignment (hd xs)) with
                    | (1, false) -> xs
                    | (_, _) -> []
                )
        | _ -> failwith "[Invalid argument] unit_propagation_applicable";;

let rec unit_propagation_applicable_f assignment formula =
    match formula with
        | Formula (Conjunction ([])) -> false
        | Formula (Conjunction (x :: xs)) -> (
                                              match (unit_propagation_applicable assignment x) with 
                                                | [] -> unit_propagation_applicable_f assignment (Formula (Conjunction (xs)))
                                                | _ -> true
                                             )
        | _ -> failwith "[Invalid argument] unit_propagation_applicable_f";;

let rec model_found assignment formula = 
    match formula with
        | Formula (Conjunction ([])) -> true 
        | Formula (Conjunction (x :: xs)) -> (
                                              match (is_clause_satisfied assignment x) with 
                                                | true -> model_found assignment (Formula (Conjunction (xs)))
                                                | false -> false
                                             )
        | _ -> failwith "[Invalid argument] model_found";;

let rec find_conflict assignment formula =
    match formula with
        | Formula (Conjunction ([])) -> []
        | Formula (Conjunction (x :: xs)) -> (
                                              match (unassigned_or_true assignment x) with 
                                                | [] -> [x]
                                                | y :: ys -> find_conflict assignment (Formula (Conjunction (xs)))   
                                             )
        (* Empty list in middle of conjunction possible? if so, another case is needed *)
        | _ -> failwith "[Invalid argument] find_conflict";;

let conflict_exists assignment formula = 
    match (find_conflict assignment formula) with 
        | [] -> false
        | x :: xs -> true
        | _ -> failwith "[Invalid argument] conflict_exists";;

let rec get_decision_literals_l assignment ls = 
    match assignment with 
        | Assignment ([]) -> ls
        | Assignment ((c, v, true, dl) :: xs) -> (get_decision_literals_l (Assignment xs) (ls @ [(c, v, true, dl)]))
        | Assignment ((c, v, false, dl) :: xs) -> (get_decision_literals_l (Assignment xs) ls)
        | _ -> failwith "[Invalid argument] get_decision_literals";;

let get_decision_literals assignment = Assignment (get_decision_literals_l assignment []);;

let rec has_decision_literals assignment =
    match assignment with 
        | Assignment ([]) -> false
        | Assignment ((c, v, true, dl) :: xs) -> true
        | Assignment ((c, v, false, dl) :: xs) -> has_decision_literals (Assignment (xs));;

(**************)
(* Basic DPLL *)
(**************)

let rec unit assignment formula = 
    match (formula, assignment) with 
        | (Formula (Conjunction ([])), Assignment ys) -> assignment
        | (Formula (Conjunction (x :: xs)), Assignment ys) -> (
                                                               match x with
                                                                | Atom (y) -> unit (Assignment (ys @ [(y, true, false, 0)])) (Formula (Conjunction (xs)))
                                                                | Not (Atom (y)) -> unit (Assignment (ys @ [(y, false, false, 0)])) (Formula (Conjunction (xs)))
                                                                | Disjunction (ys) -> unit assignment (Formula (Conjunction (xs)))
                                                                | _ -> failwith "[Invalid argument] second argument is not a formula in CNF"
                                                              )
        | _ -> failwith "[Invalid argument] second argument is not a formula in CNF"

let rec unit_propagation assignment formula dl =
    match (formula, assignment) with 
        | (Formula (Conjunction ([])), Assignment ys) -> Assignment ys
        | (Formula (Conjunction (x :: xs)), Assignment ys) -> ( 
                                                               match (unit_propagation_applicable assignment x) with
                                                                | [] -> unit_propagation (Assignment (ys)) (Formula (Conjunction (xs))) dl
                                                                | zs -> (
                                                                         match zs with
                                                                            | [Atom (z)] -> unit_propagation (Assignment (ys @ [(z, true, false, dl)])) (Formula (Conjunction (xs))) dl
                                                                            | [Not (Atom (z))] -> unit_propagation (Assignment (ys @ [(z, false, false, dl)])) (Formula (Conjunction (xs))) dl
                                                                            | _ -> failwith "[Invalid argument] unit_propagation"
                                                                        )
                                                              )
        | _ -> failwith "[Invaid argument] unit_propagation";;

let rec decide assignment clause dl =
    match (clause, assignment) with
        | (Disjunction (x :: xs), Assignment ys) -> (
                                                     match (is_assigned assignment x, x) with
                                                        | (true, _)-> decide assignment (Disjunction (xs)) dl
                                                        | (false, Atom (y)) -> (Assignment (ys @ [(y, true, true, dl + 1)]), (dl + 1))
                                                        | (false, Not (Atom (y))) -> (Assignment (ys @ [(y, false, true, dl + 1)]), (dl + 1))
                                                        | (false, _) -> failwith "[Invalid argument] decide: formula not in CNF"
                                                    )
        | _ -> failwith "[Invalid argument] decide";;

let rec decision assignment formula dl = 
    match formula with
        | Formula (Conjunction ([])) -> (assignment, dl)
        | Formula (Conjunction (x :: xs)) -> (
                                              match (is_clause_satisfied assignment x) with
                                                | true -> decision assignment (Formula (Conjunction (xs))) dl
                                                | false -> decide assignment x dl
                                             )
        | _ -> failwith "[Invalid argument] decision";;


(*************************************************************************)
(* Auxiliary functions for backjump (some use unit and unit_propagation) *)
(*************************************************************************)

let rec is_still_conflict (assignment : (constraint_n * bool * bool * int) list) formula clause =
    match assignment with
        | [] -> false 
        | x :: xs -> (
                      match (unassigned_or_true (Assignment (assignment)) clause) with
                        | [] -> true 
                        | y :: ys -> false
                     )
        | _ -> failwith "[Invalid argument] is_still_conflict";;

let rec find_minimal_i_l (assignment : (constraint_n * bool * bool * int) list) formula clause ls =
    match (is_still_conflict ls formula clause) with
        | true -> ls
        | false -> find_minimal_i_l (tl assignment) formula clause (ls @ [(hd assignment)])
        | _ -> failwith "[Invalid argument] find_minimal_i";;

let find_minimal_i (assignment : (constraint_n * bool * bool * int) list) formula clause = find_minimal_i_l assignment formula clause [];;

let rec transform_to_neg_clause assignment =
    match assignment with 
        | Assignment ([]) -> []
        | Assignment ((c, true, d, dl) :: xs) -> [Not (Atom c)] @ (transform_to_neg_clause (Assignment xs))
        | Assignment ((c, false, d, dl) :: xs) -> [Atom c] @ (transform_to_neg_clause (Assignment xs))
        | _ -> failwith "[Invalid argument] transform_to_neg_clause";;

let rec get_last_dl_literals_rec (assignment : (constraint_n * bool * bool * int) list) dl =
    match assignment with
        | (c, v, d, l) :: xs -> (
                                 match (compare l dl) with 
                                    | 0 -> assignment 
                                    | _ -> get_last_dl_literals_rec xs dl
                                )
        | _ -> failwith "[Invalid argument] get_last_dl_literals_rec";;

let get_last_dl_literals (assignment : (constraint_n * bool * bool * int) list) = 
    match (hd (rev assignment)) with
    | (c, v, d, dl) -> get_last_dl_literals_rec assignment dl
    | _ -> failwith "[Invalid argument] get_last_dl_literals";;

let rec find_backjump_clause_l (assignment : (constraint_n * bool * bool * int) list) formula clause ls = 
    match (is_still_conflict (ls @ (get_last_dl_literals assignment)) formula clause) with 
        | true -> ls @ (get_last_dl_literals assignment)
        | false -> find_backjump_clause_l (tl assignment) formula clause (ls @ [(hd assignment)])
        | _ -> failwith "[Invalid argument] find_backjump_clause";;

let find_backjump_clause (assignment : (constraint_n * bool * bool * int) list) formula clause = Disjunction (transform_to_neg_clause (get_decision_literals (Assignment (find_backjump_clause_l (find_minimal_i assignment formula clause) formula clause []))));;
        
(* Get target decision level for backjumping. *)
(* Relies on increasing order of decision levels in the assignment *)
let get_decision_level (assignment : (constraint_n * bool * bool * int) list) formula clause = 
    match (get_decision_literals (Assignment (find_backjump_clause_l assignment formula clause []))) with
    | Assignment ([]) -> failwith "[Invalid argument] get_decision_level: assignment empty"
    | Assignment ([x]) -> (
                           match x with 
                            | (c, v, d, dl) -> (dl - 1)
                            | _ -> failwith "[Invalid argument] get_decison_level"
                          )
    | Assignment (xs) -> (
                          match (hd (tl (rev xs))) with
                            | (c, v, d, dl) -> dl
                            | _ -> failwith "[Invalid argument] get_decison_level"
                         )
    | _ -> failwith "[Invalid argument] get_decision_level";;

let get_current_decision_level assignment = 
    match assignment with 
        | Assignment ([]) -> failwith "[Invalid argument] get_current_decision_level"
        | Assignment (xs) -> (
                              match (hd (rev xs)) with
                                | (c, v, d, dl) -> dl 
                             )
        | _ -> failwith "[Invalid argument] get_current_decision_level";;

(* Backjump without learning as of now *)
let rec backjump_rec assignment dl clause ls = 
    match assignment with
        | Assignment ([]) -> failwith "[Invalid argument] backjump_rec"
        | Assignment ((c, v, d, l) :: xs) -> (
                                              match (compare l dl) with
                                                | 1 -> ( 
                                                        match clause with
                                                            | Disjunction (ys) -> (
                                                                                   match (hd (rev ys)) with
                                                                                    | Atom (y) -> ls @ [(y, true, false, l)]
                                                                                    | Not (Atom (y)) -> ls @ [(y, false, false, l)]
                                                                                    | _ -> failwith "[Invalid argument] backjump_rec"
                                                                                  )
                                                            | _ -> failwith "[Invalid argument] backjump_rec"
                                                       )
                                                | 0 -> backjump_rec (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | -1 -> backjump_rec (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | _ -> failwith "[Invalid argument] backjump_rec"
                                             )
        | _ -> failwith "[Invalid argument] backjump_rec";;

let backjump assignment formula = 
    match assignment with 
        | Assignment (xs) -> let ys = (find_conflict assignment formula) in
                                Assignment (backjump_rec assignment
                                            (get_decision_level xs formula (hd ys)) 
                                            (find_backjump_clause xs formula (hd ys))
                                            [])
        | _ -> failwith "[Invalid argument] backjump";;

(* The actual DPLL procedure *)
let rec dpll_rec assignment formula dl = 
    match (model_found assignment formula) with
        | true -> true
        | false -> (
                    match (conflict_exists assignment formula) with
                        | true -> ( 
                                   match (has_decision_literals assignment) with 
                                    | false -> false
                                    | true -> let xs = (backjump assignment formula) in dpll_rec xs formula (get_current_decision_level xs)
                                  )
                        | false -> (
                                    let xs = (unit_propagation assignment formula dl) in 
                                        match (compare assignment xs) with
                                            | 0 -> (
                                                    match (decision assignment formula dl) with
                                                        | (ys, l) -> dpll_rec ys formula l
                                                   )
                                            | _ -> dpll_rec xs formula dl
                                   )
                   );;

let dpll formula = dpll_rec (unit (Assignment ([])) formula) formula 0;;

let sat formula = 
    match (dpll formula) with
        | true -> printf "SAT\n"
        | false -> printf "UNSAT\n";; 

(* Tseitin transformation to transform a formula into CNF.*)

(* Argument f is the formula and arguments n_aux and n_last are *) 
(* counting variables used to introduce the new variables needed *)
(* in the transformation algorithm *)

let remove_last xs = rev (tl (rev xs));;

let rec transform_elem (e : element) (n_aux : int) (n_last : int) : (element list * int) =
    match e with
        | Not (x) -> (
                      match (transform_elem x (n_last + 1) (n_last + 1)) with 
                        | (xs, n) -> ([Disjunction ([(Atom (AuxVar n_aux)); (Atom (AuxVar (n_last + 1)))])] @ 
                                      [Disjunction ([Not (Atom (AuxVar n_aux)); Not (Atom (AuxVar (n_last + 1)))])] @
                                      xs,
                                      n)
                        | _ -> failwith "[Invalid formula]: transform_elem"
                     )                  
        | Conjunction ([]) -> ([], n_last)
        | Conjunction (xs) -> (
                               match (length xs) with
                                | 2 -> (
                                        match (transform_elem (hd (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                        match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                        )
                                        )
                                | 1 -> (transform_elem (hd xs) n_aux n_last)
                                | _ -> (
                                        match (transform_elem (Conjunction (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                        match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                        )
                                       )
                              )
        | Disjunction ([]) -> ([], n_last)      
        | Disjunction (xs) -> (
                               match (length xs) with 
                                | 2 -> (
                                        match (transform_elem (hd (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                           match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                          )
                                       )
                                | 1 -> (transform_elem (hd xs) n_aux n_last)
                                | _ -> (
                                        match (transform_elem (Disjunction (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                        match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                        )
                                       )
                              )
        | Atom (x) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom x])] @ 
                       [Disjunction ([Not (Atom x); Atom (AuxVar n_aux)])],
                       n_last)
        | _ -> failwith "[Invalid formula]: transform_elem";;

let tseitin_transformation_n f n_aux n_last = 
    match f with
        | Formula (x) -> (
                          match (transform_elem x n_aux n_last) with
                            | (xs, n) -> Formula (Conjunction ([Atom (AuxVar n_aux)] @ xs))
                            | _ -> failwith "[Invalid formula]: tseitin_transformation_n"
                         )
        | _ -> failwith "[Invalid formula]: tseitin_transformation_n";;

let tseitin_transformation f = tseitin_transformation_n f 0 0;;
                               