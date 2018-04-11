open String
open Types
open List
open Core.Std

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
                                    | _ -> failwith "[Invalid argument] second argument is not a literal"
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
                                                                        | _ -> is_assigned (Assignment xs) literal
                                                                      )
                                    | ((y, false, d, dl), Not (Atom (z))) -> (
                                                                              match (compare y z) with 
                                                                                | 0 -> true
                                                                                | _ -> is_assigned (Assignment xs) literal
                                                                             )   
                                    | _ -> failwith "[Invalid argument] second argument is not a literal"
                                  )
        | _ -> failwith "[Invalid argument] first argument is not a constraint_n * bool list";;        

let rec is_clause_satisfied assignment clause =
    match clause with 
        | Disjunction ([]) -> false
        | Disjunction (x :: xs) -> (
                                    match is_true assignment x with
                                    | true -> true
                                    | false -> is_clause_satisfied assignment (Disjunction (xs))
                                   )
        | _ -> failwith "[Invalid argument] second argument is not a Disjunction of element list";;

let rec unassigned_or_true_l assignment clause ls =
    match clause with
        | Atom (x) -> (
                       match (is_true assignment (Atom (x))) with
                        | false -> [Atom (x)]
                        | true -> []
                      )
        | Not (Atom (x)) -> (
                             match (is_true assignment (Not (Atom (x)))) with
                                | false -> [Not (Atom (x))]
                                | true -> []
                            )
        | Disjunction ([]) -> ls
        | Disjunction (x :: xs) -> (
                                   match (is_true assignment x) with
                                    | false -> unassigned_or_true_l assignment (Disjunction (xs)) (ls @ [x])
                                    | true -> unassigned_or_true_l assignment (Disjunction (xs)) ls
                                    | _ -> failwith "[Invalid argument] unassigned_or_truel"
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
                                                | x :: xs -> find_conflict assignment (Formula (Conjunction (xs)))   
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
                                                                | _ -> failwith "[Invalid argument] unit_propagation"
                                                              )
        | _ -> failwith "[Invaid argument] unit_propagation";;

let rec decision assignment formula dl = 
    match (formula, assignment) with
        | (Formula (Conjunction ([])), Assignment ys) -> (Assignment ys, dl)
        | (Formula (Conjunction (x :: xs)), Assignment ys) -> (
                                                               match (is_clause_satisfied assignment x, x) with
                                                                | (true, _) -> decision (Assignment ys) (Formula (Conjunction (xs))) dl
                                                                | (false, Atom (y)) -> (
                                                                                        match (is_assigned assignment x) with
                                                                                            | true -> decision (Assignment ys) (Formula (Conjunction (xs))) dl
                                                                                            | false -> (Assignment (ys @ [(y, true, true, dl + 1)]), (dl + 1))
                                                                                       )
                                                                | (false, Not (Atom (y))) -> (
                                                                                              match (is_assigned assignment x) with
                                                                                                | true -> decision (Assignment ys) (Formula (Conjunction (xs))) dl
                                                                                                | false -> (Assignment (ys @ [(y, false, true, dl + 1)]), (dl + 1))
                                                                                             )
                                                                | _ -> failwith "[Invalid argument] decision"
                                                              )
        | _ -> failwith "[Invalid argument] decision";;


(*************************************************************************)
(* Auxiliary functions for backjump (some use unit and unit_propagation) *)
(*************************************************************************)

let rec is_still_conflict assignment formula clause =
    match assignment with
        | [] -> false 
        | x :: xs -> (
                      match (unassigned_or_true (unit_propagation (unit (Assignment (assignment)) formula) formula 0) clause) with
                        | [] -> true 
                        | y :: ys -> false
                     )
        | _ -> failwith "[Invalid argument] is_still_conflict";;

let rec find_minimal_i_l assignment formula clause ls =
    match (is_still_conflict ls formula clause) with
        | true -> ls
        | false -> find_minimal_i_l (tl assignment) formula clause (ls @ (hd assignment))
        | _ -> failwith "[Invalid argument] find_minimal_i";;

let find_minimal_i assignment formula clause = find_minimal_i_l assignment formula clause [];;

let rec transform_to_neg_clause assignment =
    match assignment with 
        | Assignment ([]) -> []
        | Assignment ((c, true, d, dl) :: xs) -> [Not (Atom c)] @ (transform_to_neg_clause (Assignment xs))
        | Assignment ((c, false, d, dl) :: xs) -> [Atom c] @ (transform_to_neg_clause (Assignment xs))
        | _ -> failwith "[Invalid argument] transform_to_neg_clause";;

let rec find_backjump_clause_l assignment formula clause ls = 
    match (is_still_conflict (ls @ (hd (rev assignment))) formula clause) with 
        | true -> ls @ (hd (rev assignment))
        | false -> find_backjump_clause_l (tl assignment) formula clause (ls @ (hd assignment))
        | _ -> failwith "[Invalid argument] find_backjump_clause";;

let find_backjump_clause assignment formula clause = Disjunction (transform_to_neg_clause (Assignment (find_backjump_clause_l assignment formula clause [])));;
        
(* Get target decision level for backjumping. *)
(* Relies on increasing order of decision levels in the assignment *)
let get_decision_level assignment formula clause = 
    match (find_backjump_clause_l assignment formula clause []) with
    | [] -> failwith "[Invalid argument] get_decision_level: assignment empty"
    | [x] -> failwith "[Invalid argument] get_decision_level: assignment contains just one literal"
    | xs-> (
            match (hd (tl (rev xs))) with
            | (c, v, d, dl) -> dl
            | _ -> failwith "[Invalid argument] get_decison_level"
           )
    | _ -> failwith "[Invalid argument] get_decision_level";;

(* TODO: get_current_decision_level for after backjump *)

(* Backjump without learning as of now *)
let rec backjump_rec assignment dl clause ls = 
    match assignment with
        | Assignment ([]) -> failwith "[Invalid argument] backjump"
        | Assignment ((c, v, d, l) :: xs) -> (
                                              match (compare l dl) with
                                                | 0 -> ( 
                                                        match clause with
                                                            | Disjunction (ys) -> (
                                                                                   match (hd (rev ys)) with
                                                                                    | Atom (y) -> ls @ [(c, v, d, l)] @ [(y, true, false, l)]
                                                                                    | Not (Atom (y)) -> ls @ [(c, v, d, l)] @ [(y, false, false, l)]
                                                                                    | _ -> failwith "[Invalid argument] backjump"
                                                                                  )
                                                            | _ -> failwith "[Invalid argument] backjump"
                                                       )
                                                | -1 -> backjump_rec (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | _ -> failwith "[Invalid argument] backjump"
                                             )
        | _ -> failwith "[Invalid argument] backjump";;

let backjump assignment formula = 
    match assignment with 
        | Assignment (xs) -> Assignment (backjump_rec assignment
                                                      (get_decision_level xs formula (find_conflict assignment formula)) 
                                                      (find_backjump_clause assignment formula (find_conflict assignment formula))
                                                      [])
        | _ -> failwith "[Invalid argument] backjump";;

(* Tseitin transformation to transform a formula into CNF.*)

(* Argument f is the formula and arguments n_aux and n_last are *) 
(* counting variables used to introduce the new variables needed *)
(* in the transformation algorithm *)

let remove_last xs = rev (tl (rev xs));;

let rec transform_elem (e : element) (n_aux : int) (n_last : int) : element list =
    match e with
        | Not (x) -> [Disjunction ([(Atom (AuxVar n_aux)); (Atom (AuxVar (n_last + 1)))])] @ 
                     [Disjunction ([Not (Atom (AuxVar n_aux)); Not (Atom (AuxVar (n_last + 1)))])] @
                     transform_elem x (n_last + 1) (n_last + 1)
        | Conjunction ([]) -> []
        | Conjunction (xs) -> [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                              [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                              [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                              transform_elem (Conjunction (remove_last xs)) (n_last + 1) (n_last + 2) @
                              transform_elem (hd (rev xs)) (n_last + 2) (n_last + 2)                      
        | Disjunction ([]) -> []      
        | Disjunction (xs) -> [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                              [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                              [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                              transform_elem (Disjunction (remove_last xs)) (n_last + 1) (n_last + 2) @
                              transform_elem (hd (rev xs)) (n_last + 2) (n_last + 2) 
        | Atom (x) -> [Disjunction ([Not (Atom (AuxVar n_aux)); Atom x])] @ 
                      [Disjunction ([Not (Atom x); Atom (AuxVar n_aux)])]
        | _ -> failwith "[Invalid formula]: transform_elem";;

let tseitin_transformation_n f n_aux n_last = 
    match f with
        | Formula (x) -> Formula (Conjunction ([Atom (AuxVar n_aux)] @ (transform_elem x n_aux n_last)))
        | _ -> failwith "[Invalid formula]: tseitin_transformation_n"

let tseitin_transformation f = tseitin_transformation_n f 0 0;;

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