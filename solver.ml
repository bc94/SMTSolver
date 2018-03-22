open String
open Types

let rec print_num_type n = 
    match n with
        | Sum (x, y) -> "Sum (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")" 
        | Prod (x, y) -> "Prod (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")"
        | Num (x) -> "Num " ^ (string_of_int x)
        | Var (x) -> "Var " ^ x
        | _ -> failwith "[Invalid formula]: print_num_type"

let print_less_equal le =
    match le with
        | LessEq (x, y) -> "LessEq (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")"
        | _ -> failwith "[Invalid formula]: print_less_equal"

let print_constraint_n c = 
    match c with
        | Constraint (x, y) ->  "Constraint (" ^ (string_of_int x) ^ ", (" ^ (print_less_equal y) ^ "))"        
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
        | Formula (x) -> "Formula (" ^ (print_element x) ^ ")"
        | _ -> failwith "[Invalid formula]"