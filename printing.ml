open String
open Types
open Simplex
open Simplex_inc
open Big_int
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
        | Div (x, y) -> "Div (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")"
        | Num (x) -> "Num (" ^ (string_of_int x) ^ ")"
        | Var (x) -> "Var (" ^ x ^ ")"
        | _ -> failwith "[Invalid formula]: print_num_type"

let print_less_equal le =
    match le with
        | LessEq (x, y) -> "LessEq (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")"
        | Eq (x, y) -> "Eq (" ^ (print_num_type x) ^ ", " ^ (print_num_type y) ^ ")"
        | _ -> failwith "[Invalid formula]: print_less_equal"

let print_constraint_n c = 
    match c with
        | Constraint (x) ->  "Constraint (" ^ (print_less_equal x) ^ ")"  
        | AuxVar (x) -> "AuxVar (" ^ (string_of_int x) ^ ")"      
        | Index (x) -> "Index (" ^ (string_of_int x) ^ ")"
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

(* Functions for printing an assignment *)

let rec print_assignment_rec assignment =
    match assignment with 
        | Assignment ([]) -> ""
        | Assignment ((y, b, d, dl) :: xs) -> "(" ^ (print_constraint_n y) ^ ", " ^ (string_of_bool b) ^ ", " ^ (string_of_bool d) ^ ", " ^ (string_of_int dl) ^ "); " ^ (print_assignment_rec (Assignment (xs)));;

let print_assignment assignment = printf "Assignment (%s)\n" (print_assignment_rec assignment);;

(* Functions for printing constraints in simplex format *)

let rec fmaplist_to_string l =
    match l with
        | [] -> ""
        | ((Simplex.Nat n), (Simplex.Frct (x, y))) :: xs -> " + (" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y))) ^ ") * " ^ (string_of_int (int_of_big_int n)) ^ (fmaplist_to_string xs);;

let rec fmaplist_to_string_inc l =
    match l with
        | [] -> ""
        | ((Simplex_inc.Nat n), (Simplex_inc.Frct (x, y))) :: xs -> " + (" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y))) ^ ") * " ^ (string_of_int (int_of_big_int n)) ^ (fmaplist_to_string_inc xs);;

let rec print_simplex_constraints_rec constraints = 
    match constraints with
        | [] -> "\n";
        | (Simplex.LEQ ((Simplex.LinearPoly (Simplex.Fmap_of_list (((Simplex.Nat n), (Simplex.Frct (x1, y1))) :: ns))), (Simplex.Frct (x2, y2)))) :: cs -> 
                        "((" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n)) ^ fmaplist_to_string ns ^ " <= (" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y2))) ^ "))\n" ^ print_simplex_constraints_rec cs
        | (Simplex.GEQ ((Simplex.LinearPoly (Simplex.Fmap_of_list (((Simplex.Nat n), (Simplex.Frct (x1, y1))) :: ns))), (Simplex.Frct (x2, y2)))) :: cs ->
                        "((" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n)) ^ fmaplist_to_string ns ^ " >= (" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y2))) ^ "))\n" ^ print_simplex_constraints_rec cs
        | (Simplex.LEQPP ((Simplex.LinearPoly (Simplex.Fmap_of_list (((Simplex.Nat n1), (Simplex.Frct (x1, y1))) :: n1s))), (Simplex.LinearPoly (Simplex.Fmap_of_list (((Simplex.Nat n2), (Simplex.Frct (x2, y2))) :: n2s))))) :: cs ->
                        "((" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n1)) ^ fmaplist_to_string n1s ^ " <= (" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y2))) ^ ") * " ^ (string_of_int (int_of_big_int n2)) ^ fmaplist_to_string n2s ^ ")\n" ^ print_simplex_constraints_rec cs
        | (Simplex.GTPP ((Simplex.LinearPoly (Simplex.Fmap_of_list (((Simplex.Nat n1), (Simplex.Frct (x1, y1))) :: n1s))), (Simplex.LinearPoly (Simplex.Fmap_of_list (((Simplex.Nat n2), (Simplex.Frct (x2, y2))) :: n2s))))) :: cs -> 
                        "((" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n1)) ^ fmaplist_to_string n1s ^ " > (" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex.integer_of_int y2))) ^ ") * " ^ (string_of_int (int_of_big_int n2)) ^ fmaplist_to_string n2s ^ ")\n" ^ print_simplex_constraints_rec cs
        | _ -> failwith "[Invalid argument] print_simplex_constraints";;

let print_simplex_constraints constraints = printf "Simplex constraints: \n%s\n" (print_simplex_constraints_rec constraints);;

let rec print_simplex_constraints_inc_rec constraints = 
    match constraints with
        | [] -> "\n";
        | (x, Simplex_inc.LEQ ((Simplex_inc.LinearPoly (Simplex_inc.Fmap_of_list (((Simplex_inc.Nat n), (Simplex_inc.Frct (x1, y1))) :: ns))), (Simplex_inc.Frct (x2, y2)))) :: cs -> 
                        "(" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_nat x))) ^ ") ((" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n)) ^ fmaplist_to_string_inc ns ^ " <= (" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y2))) ^ "))\n" ^ print_simplex_constraints_inc_rec cs
        | (x, Simplex_inc.GEQ ((Simplex_inc.LinearPoly (Simplex_inc.Fmap_of_list (((Simplex_inc.Nat n), (Simplex_inc.Frct (x1, y1))) :: ns))), (Simplex_inc.Frct (x2, y2)))) :: cs ->
                        "(" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_nat x))) ^ ") ((" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n)) ^ fmaplist_to_string_inc ns ^ " >= (" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y2))) ^ "))\n" ^ print_simplex_constraints_inc_rec cs
        | (x, Simplex_inc.LEQPP ((Simplex_inc.LinearPoly (Simplex_inc.Fmap_of_list (((Simplex_inc.Nat n1), (Simplex_inc.Frct (x1, y1))) :: n1s))), (Simplex_inc.LinearPoly (Simplex_inc.Fmap_of_list (((Simplex_inc.Nat n2), (Simplex_inc.Frct (x2, y2))) :: n2s))))) :: cs ->
                        "(" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_nat x))) ^ ") ((" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n1)) ^ fmaplist_to_string_inc n1s ^ " <= (" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y2))) ^ ") * " ^ (string_of_int (int_of_big_int n2)) ^ fmaplist_to_string_inc n2s ^ ")\n" ^ print_simplex_constraints_inc_rec cs
        | (x, Simplex_inc.GTPP ((Simplex_inc.LinearPoly (Simplex_inc.Fmap_of_list (((Simplex_inc.Nat n1), (Simplex_inc.Frct (x1, y1))) :: n1s))), (Simplex_inc.LinearPoly (Simplex_inc.Fmap_of_list (((Simplex_inc.Nat n2), (Simplex_inc.Frct (x2, y2))) :: n2s))))) :: cs -> 
                        "(" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_nat x))) ^ ") ((" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x1))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y1))) ^ ") * " ^ (string_of_int (int_of_big_int n1)) ^ fmaplist_to_string_inc n1s ^ " > (" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int x2))) ^ "/" ^ (string_of_int (int_of_big_int (Simplex_inc.integer_of_int y2))) ^ ") * " ^ (string_of_int (int_of_big_int n2)) ^ fmaplist_to_string_inc n2s ^ ")\n" ^ print_simplex_constraints_inc_rec cs
        | _ -> failwith "[Invalid argument] print_simplex_constraints_inc";;

let print_simplex_constraints_inc constraints = printf "Simplex constraints: \n%s\n" (print_simplex_constraints_inc_rec constraints);;