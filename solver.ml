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
                                    | ((y, b, d), Atom (z)) -> ( 
                                                                match (compare y z) with 
                                                                | 0 -> true
                                                                | _ -> is_assigned (Assignment xs) literal
                                                               )
                                    | ((y, b, d), Not (Atom (z))) -> (
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
                                    | ((y, true, d), Atom (z)) -> ( 
                                                                    match (compare y z) with 
                                                                    | 0 -> true
                                                                    | _ -> is_assigned (Assignment xs) literal
                                                                  )
                                    | ((y, false, d), Not (Atom (z))) -> (
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
        
(**************)
(* Basic DPLL *)
(**************)

let rec unit assignment formula = 
    match (formula, assignment) with 
        | (Formula (Conjunction ([])), Assignment ys) -> assignment
        | (Formula (Conjunction (x :: xs)), Assignment ys) -> (
                                                               match x with
                                                                | Atom (y) -> unit (Assignment (ys @ [(y, true, false)])) (Formula (Conjunction (xs)))
                                                                | Not (Atom (y)) -> unit (Assignment (ys @ [(y, false, false)])) (Formula (Conjunction (xs)))
                                                                | Disjunction (ys) -> unit assignment (Formula (Conjunction (xs)))
                                                                | _ -> failwith "[Invalid argument] second argument is not a formula in CNF"
                                                              )
        | _ -> failwith "[Invalid argument] second argument is not a formula in CNF"

let rec unit_propagation assignment formula =
    match (formula, assignment) with 
        | (Formula (Conjunction ([])), Assignment ys) -> Assignment ys
        | (Formula (Conjunction (x :: xs)), Assignment ys) -> ( 
                                                               match (unit_propagation_applicable assignment x) with
                                                                | [] -> unit_propagation (Assignment (ys)) (Formula (Conjunction (xs)))
                                                                | zs -> (
                                                                         match zs with
                                                                            | [Atom (z)] -> unit_propagation (Assignment (ys @ [(z, true, false)])) (Formula (Conjunction (xs)))
                                                                            | [Not (Atom (z))] -> unit_propagation (Assignment (ys @ [(z, false, false)])) (Formula (Conjunction (xs)))
                                                                            | _ -> failwith "[Invalid argument] unit_propagation"
                                                                        )
                                                                | _ -> failwith "[Invalid argument] unit_propagation"
                                                              )
        | _ -> failwith "[Invaid argument] unit_propagation";;

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