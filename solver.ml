open String
open Types
open Core.Std

(* Tseitin transformation to transform a formula into CNF.*)

(* Argument f is the formula and argument n is a counting *)
(* variable used to introduce the new variables needed in *)
(* the transformation algorithm *)

let transform_elem_list el n =
    match el with
        | Not (x) -> (Disjunction ([Atom (AuxVar n), Atom (AuxVar (n + 1))])) @ 
                     (Disjunction ([Not (Atom (AuxVar n)), Not (Atom (AuxVar (n + 1)))])) @
                     transform_elem_list x (n + 1)
        | Conjunction (xs) ->         
        | Disjunction (xs) ->
        | Atom (x) -> (Disjunction ([Not (Atom (AuxVar n)), Atom x])) @ 
                      (Disjunction ([Not (Atom x), Atom (AuxVar n)]))
        | _ -> failwith "[Invalid formula]: transform_elem_list";;

let tseitin_transformation_n f n = 
    match f with
        | Formula (x) -> Formula (Conjunction ( (Atom (AuxVar n)) :: (transform_elem_list x n)))
        | _ -> failwith "[Invalid formula]: tseitin_transformation_n"

let tseitin_transformation f = tseitin_transformation_n f 0;;

(* Functions for printing a formula *)

let rec print_num_type_list nl = 
    match nl with
        | x :: xs -> (print_num_type x) ^ ", " ^ (print_num_type_list xs)
        | [] -> "[]"

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
        | Constraint (x) ->  "Constraint (" ^ (print_less_equal x) ^ "))"        
        | _ -> failwith "[Invalid formula]: print_constraint_n"

let rec print_element_list el = 
    match el with
        | x :: xs -> (print_element x) ^ ", " ^ (print_element_list xs)
        | [] -> "[]"

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