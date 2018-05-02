open String
open Types
open Core.Std

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

(* Function for printing an assignment *)

let rec print_assignment_rec assignment =
    match assignment with 
        | Assignment ([]) -> ""
        | Assignment ((y, b, d, dl) :: xs) -> "(" ^ (print_constraint_n y) ^ ", " ^ (string_of_bool b) ^ ", " ^ (string_of_bool d) ^ ", " ^ (string_of_int dl) ^ "); " ^ (print_assignment_rec (Assignment (xs)));;

let print_assignment assignment = printf "Assignment (%s)\n" (print_assignment_rec assignment);;