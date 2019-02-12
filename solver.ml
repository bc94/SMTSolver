module TWL_Map = Map.Make(String);;
module PS_Map = Map.Make(struct type t = int let compare = compare end);;
module UP_Map = Map.Make(String);;
module Assignment_Map = Map.Make(struct type t = int let compare = compare end);;

open String
open Types
open List
open Big_int
open Core.Std
open Simplex
open Simplex_inc

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
                                  );;

let rec is_assigned_i (assignment : assignment) (literal : element) =
    match assignment with
        | Assignment ([]) -> false
        | Assignment (x :: xs) -> (
                                   match (x, literal) with 
                                    | ((Index (_), _, _, _), Atom (AuxVar (_))) -> is_assigned_i (Assignment xs) literal
                                    | ((Index (_), _, _,_ ), Not (Atom (AuxVar (_)))) -> is_assigned_i (Assignment xs) literal
                                    | ((AuxVar (_), _, _, _), Atom (Index (_))) -> is_assigned_i (Assignment xs) literal
                                    | ((AuxVar (_), _, _, _), Not (Atom (Index (_)))) -> is_assigned_i (Assignment xs) literal
                                    | ((AuxVar (y), b, d, dl), Atom (AuxVar (z))) -> (
                                                                                    match (compare y z) with
                                                                                        | 0 -> true
                                                                                        | _ -> is_assigned_i (Assignment xs) literal
                                                                                     )
                                    | ((AuxVar (y), b, d, dl), Not (Atom (AuxVar (z)))) -> (
                                                                                            match (compare y z) with
                                                                                                | 0 -> true
                                                                                                | _ -> is_assigned_i (Assignment xs) literal
                                                                                           )
                                    | ((Index (y), b, d, dl), Atom (Index (z))) -> ( 
                                                                    match (compare y z) with
                                                                    | 0 -> true
                                                                    | _ -> is_assigned_i (Assignment xs) literal
                                                                   )
                                    | ((Index (y), b, d, dl), Not (Atom (Index (z)))) -> (
                                                                          match (compare y z) with 
                                                                            | 0 -> true
                                                                            | _ -> is_assigned_i (Assignment xs) literal
                                                                         )
                                    | _ -> failwith "[Invalid argument] is_assigned_i: second argument is not a literal or non-indexed representations are used"
                                  );;

let rec is_assigned_i_map assignment assigned_map literal = 
    let (indexed, aux) = assigned_map in
    match literal with 
        | Atom (Index (x)) -> Assignment_Map.mem x indexed
        | Atom (AuxVar (x)) -> Assignment_Map.mem x aux
        | Not (Atom (Index (x))) -> Assignment_Map.mem x indexed
        | Not (Atom (AuxVar (x))) -> Assignment_Map.mem x aux
        | _ -> failwith "[Invalid argument] is_assigned_i_map: second argument is not a literal or non-indexed representations are used";;

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
                                  );;    

let rec is_true_i (assignment : assignment) (literal : element) = 
    match assignment with
        | Assignment ([]) -> false
        | Assignment (x :: xs) -> (
                                   match (x, literal) with 
                                    | ((AuxVar (_), _, _, _), Atom (Index (_))) -> is_true_i (Assignment xs) literal
                                    | ((AuxVar (_), _, _, _), Not (Atom (Index (_)))) -> is_true_i (Assignment xs) literal
                                    | ((Index (_), _, _, _), Atom (AuxVar (_))) -> is_true_i (Assignment xs) literal
                                    | ((Index (_), _, _, _), Not (Atom (AuxVar (_)))) -> is_true_i (Assignment xs) literal
                                    | ((AuxVar (y), true, d, dl), Atom (AuxVar (z))) -> (
                                                                                         match (compare y z) with
                                                                                            | 0 -> true
                                                                                            | _ -> is_true_i (Assignment xs) literal
                                                                                        )
                                    | ((AuxVar (y), false, d, dl), Not (Atom (AuxVar (z)))) -> (
                                                                                                match (compare y z) with
                                                                                                    | 0 -> true
                                                                                                    | _ -> is_true_i (Assignment xs) literal
                                                                                               )
                                    | ((AuxVar (y), true, d, dl), Not (Atom (AuxVar (z)))) -> is_true_i (Assignment xs) literal
                                    | ((AuxVar (y), false, d, dl), Atom (AuxVar (z))) -> is_true_i (Assignment xs) literal
                                    | ((Index (y), true, d, dl), Atom (Index (z))) -> ( 
                                                                       match (compare y z) with 
                                                                        | 0 -> true
                                                                        | _ -> is_true_i (Assignment xs) literal
                                                                      )
                                    | ((Index (y), true, d, dl), Not (Atom (Index (z)))) -> is_true_i (Assignment xs) literal
                                    | ((Index (y), false, d, dl), Not (Atom (Index (z)))) -> (
                                                                              match (compare y z) with 
                                                                                | 0 -> true
                                                                                | _ -> is_true_i (Assignment xs) literal
                                                                             )   
                                    | ((Index (y), false, d, dl), Atom (Index (z))) -> is_true_i (Assignment xs) literal
                                    | _ -> failwith "[Invalid argument] is_true_i: second argument not a literal or non-indexed representation is used"
                                  );;    

let rec is_true_i_map assignment assigned_map literal = 
    let (indexed, aux) = assigned_map in
    match literal with 
        | Atom (Index (x)) -> if Assignment_Map.mem x indexed
                              then Assignment_Map.find x indexed
                              else false
        | Atom (AuxVar (x)) -> if Assignment_Map.mem x aux
                               then Assignment_Map.find x aux
                               else false
        | Not (Atom (Index (x))) -> if Assignment_Map.mem x indexed
                                    then ( 
                                          if Assignment_Map.find x indexed
                                          then false 
                                          else true
                                         )
                                    else false
        | Not (Atom (AuxVar (x))) -> if Assignment_Map.mem x aux
                                     then ( 
                                          if Assignment_Map.find x aux
                                          then false 
                                          else true
                                         )
                                     else false
        | _ -> failwith "[Invalid argument] is_true_i_map: second argument is not a literal or non-indexed representations are used";;

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
        | _ -> failwith "[Invalid argument] is_clause_satisfied: second argument is not a Disjunction of element list";;

let rec is_clause_satisfied_i assignment clause =
    match clause with 
        | Disjunction ([]) -> false
        | Disjunction (x :: xs) -> (*if exists (fun x -> is_true_i assignment x) (x :: xs)
                                   then true 
                                   else false*)
                                   (
                                    match (is_true_i assignment x) with
                                    | true -> true
                                    | false -> is_clause_satisfied_i assignment (Disjunction (xs))
                                   )
        | Atom (x) -> (
                       match (is_true_i assignment clause) with
                        | true -> true
                        | false -> false
                      )
        | Not (Atom (x)) -> (
                             match (is_true_i assignment clause) with
                                | true -> true
                                | false -> false
                            )
        | _ -> failwith "[Invalid argument] is_clause_satisfied_i: second argument is not a Disjunction of element list";;

let rec is_clause_satisfied_i_map assignment assigned_map clause =
    match clause with 
        | Disjunction ([]) -> false
        | Disjunction (x :: xs) -> (
                                    match (is_true_i_map assignment assigned_map x) with
                                    | true -> true
                                    | false -> is_clause_satisfied_i_map assignment assigned_map (Disjunction (xs))
                                   )
        | Atom (x) -> (
                       match (is_true_i_map assignment assigned_map clause) with
                        | true -> true
                        | false -> false
                      )
        | Not (Atom (x)) -> (
                             match (is_true_i_map assignment assigned_map clause) with
                                | true -> true
                                | false -> false
                            )
        | _ -> failwith "[Invalid argument] is_clause_satisfied_i_map: second argument is not a Disjunction of element list";;

let rec contains_unassigned_literal assignment clause = 
    match clause with
        | Disjunction ([]) -> false
        | Disjunction (x :: xs) -> (
                                    match (is_assigned assignment x) with
                                        | true -> contains_unassigned_literal assignment (Disjunction (xs))
                                        | false -> true
                                   )
        | Atom (x) -> (
                       match (is_assigned assignment clause) with
                        | true -> false 
                        | false -> true
                      )
        | Not (Atom (x)) -> (
                             match (is_assigned assignment clause) with
                                | true -> false 
                                | false -> true
                            )
        | _ -> failwith "[Invalid argument] contains_unassigned_literal: argument neither a clause nor a literal";;

let rec contains_unassigned_literal_i assignment clause = 
    match clause with
        | Disjunction ([]) -> false
        | Disjunction (x :: xs) -> (
                                    match (is_assigned_i assignment x) with
                                        | true -> contains_unassigned_literal_i assignment (Disjunction (xs))
                                        | false -> true
                                   )
        | Atom (x) -> (
                       match (is_assigned_i assignment clause) with
                        | true -> false 
                        | false -> true
                      )
        | Not (Atom (x)) -> (
                             match (is_assigned_i assignment clause) with
                                | true -> false 
                                | false -> true
                            )
        | _ -> failwith "[Invalid argument] contains_unassigned_literal_i: argument neither a clause nor a literal";;

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
                                  )
        | _ -> failwith "[Invalid argument] unassigned_or_true_l";;

let unassigned_or_true assignment clause = unassigned_or_true_l assignment clause [];;

let rec true_or_unassigned_combined assignment literal = 
    match assignment with
        | Assignment ([]) -> true
        | Assignment (x :: xs) -> (
                                   match (x, literal) with 
                                    | ((Index (_), _, _, _), Atom (AuxVar (_))) -> true_or_unassigned_combined (Assignment xs) literal
                                    | ((Index (_), _, _,_ ), Not (Atom (AuxVar (_)))) -> true_or_unassigned_combined (Assignment xs) literal
                                    | ((AuxVar (_), _, _, _), Atom (Index (_))) -> true_or_unassigned_combined (Assignment xs) literal
                                    | ((AuxVar (_), _, _, _), Not (Atom (Index (_)))) -> true_or_unassigned_combined (Assignment xs) literal
                                    | ((AuxVar (y), v, d, dl), Atom (AuxVar (z))) -> (
                                                                                    match (compare y z) with
                                                                                        | 0 -> if v 
                                                                                               then true 
                                                                                               else false 
                                                                                        | _ -> true_or_unassigned_combined (Assignment xs) literal
                                                                                     )
                                    | ((AuxVar (y), v, d, dl), Not (Atom (AuxVar (z)))) -> (
                                                                                            match (compare y z) with
                                                                                                | 0 -> if v 
                                                                                                       then false 
                                                                                                       else true
                                                                                                | _ -> true_or_unassigned_combined (Assignment xs) literal
                                                                                           )
                                    | ((Index (y), v, d, dl), Atom (Index (z))) -> ( 
                                                                    match (compare y z) with
                                                                    | 0 -> if v 
                                                                           then true 
                                                                           else false
                                                                    | _ -> true_or_unassigned_combined (Assignment xs) literal
                                                                   )
                                    | ((Index (y), v, d, dl), Not (Atom (Index (z)))) -> (
                                                                          match (compare y z) with 
                                                                            | 0 -> if v 
                                                                                   then false
                                                                                   else true
                                                                            | _ -> true_or_unassigned_combined (Assignment xs) literal
                                                                         )
                                    | _ -> failwith "[Invalid argument] is_assigned_i: second argument is not a literal or non-indexed representations are used"
                                  );;

let rec true_or_unassigned_combined_map assignment assigned_map literal = 
    let (indexed, aux) = assigned_map in
    match literal with 
        | Atom (Index (x)) -> if Assignment_Map.mem x indexed
                              then Assignment_Map.find x indexed
                              else true
        | Atom (AuxVar (x)) -> if Assignment_Map.mem x aux
                               then Assignment_Map.find x aux
                               else true
        | Not (Atom (Index (x))) -> if Assignment_Map.mem x indexed
                                    then ( 
                                          if Assignment_Map.find x indexed
                                          then false 
                                          else true
                                         )
                                    else true
        | Not (Atom (AuxVar (x))) -> if Assignment_Map.mem x aux
                                     then ( 
                                          if Assignment_Map.find x aux
                                          then false
                                          else true
                                         )
                                     else true
        | _ -> failwith "[Invalid argument] true_or_unassigned_combined_map: third argument is not a literal or non-indexed representations are used";;

let rec unassigned_or_true_i_l assignment clause ls =
    match clause with
        | Atom (x) -> (
                       match (is_true_i assignment (Atom (x))) with
                        | true -> [Atom (x)]
                        | false -> []
                      )
        | Not (Atom (x)) -> (
                             match (is_true_i assignment (Not (Atom (x)))) with
                                | true -> [Not (Atom (x))]
                                | false -> []
                            )
        | Disjunction ([]) -> ls
        | Disjunction (x :: xs) -> (
                                    match true_or_unassigned_combined assignment x with
                                        | true -> unassigned_or_true_i_l assignment (Disjunction (xs)) (ls @ [x])
                                        | false -> unassigned_or_true_i_l assignment (Disjunction (xs)) ls
                                   )
        | _ -> failwith "[Invalid argument] unassigned_or_true_i_l";;

let unassigned_or_true_i assignment clause = unassigned_or_true_i_l assignment clause [];;

let rec unassigned_or_true_i_l_map assignment assigned_map clause ls =
    match clause with
        | Atom (x) -> (
                       match (is_true_i_map assignment assigned_map (Atom (x))) with
                        | true -> [Atom (x)]
                        | false -> []
                      )
        | Not (Atom (x)) -> (
                             match (is_true_i_map assignment assigned_map (Not (Atom (x)))) with
                                | true -> [Not (Atom (x))]
                                | false -> []
                            )
        | Disjunction ([]) -> ls
        | Disjunction (x :: xs) -> (
                                    match true_or_unassigned_combined_map assignment assigned_map x with
                                        | true -> unassigned_or_true_i_l_map assignment assigned_map (Disjunction (xs)) (ls @ [x])
                                        | false -> unassigned_or_true_i_l_map assignment assigned_map (Disjunction (xs)) ls
                                   )
        | _ -> failwith "[Invalid argument] unassigned_or_true_i_l_map";;

let unassigned_or_true_i_map assignment assigned_map clause = unassigned_or_true_i_l_map assignment assigned_map clause [];;

let rec get_first_unassigned_var assignment clause =
    match clause with
        | Atom (x) -> (
                       match (is_assigned_i assignment (Atom (x))) with
                        | true -> []
                        | false -> [Atom (x)]
                      )
        | Not (Atom (x)) -> (
                             match (is_assigned_i assignment (Not (Atom (x)))) with
                                | true -> []
                                | false -> [Not (Atom (x))]
                            )
        | Disjunction ([]) -> []
        | Disjunction (x :: xs) -> (
                                    match is_assigned_i assignment x with
                                        | true -> get_first_unassigned_var assignment (Disjunction (xs)) 
                                        | false -> [x]
                                   )
        | _ -> failwith "[Invalid argument] get_first_unassigned_var";;

let rec get_first_unassigned_var_map assignment assigned_map clause =
    match clause with
        | Atom (x) -> (
                       match (is_assigned_i_map assignment assigned_map (Atom (x))) with
                        | true -> []
                        | false -> [Atom (x)]
                      )
        | Not (Atom (x)) -> (
                             match (is_assigned_i_map assignment assigned_map (Not (Atom (x)))) with
                                | true -> []
                                | false -> [Not (Atom (x))]
                            )
        | Disjunction ([]) -> []
        | Disjunction (x :: xs) -> (
                                    match is_assigned_i_map assignment assigned_map x with
                                        | true -> get_first_unassigned_var_map assignment assigned_map (Disjunction (xs)) 
                                        | false -> [x]
                                   )
        | _ -> failwith "[Invalid argument] get_first_unassigned_var_map";;

let unit_propagation_applicable assignment clause =
    match (unassigned_or_true assignment clause) with
        | [] -> []
        | xs -> (
                 match (length xs, is_assigned assignment (hd xs)) with
                    | (1, false) -> xs
                    | (_, _) -> []
                );;

let rec unit_propagation_applicable_f assignment formula =
    match formula with
        | Formula (Conjunction ([])) -> false
        | Formula (Conjunction (x :: xs)) -> (
                                              match (unit_propagation_applicable assignment x) with 
                                                | [] -> unit_propagation_applicable_f assignment (Formula (Conjunction (xs)))
                                                | _ -> true
                                             )
        | _ -> failwith "[Invalid argument] unit_propagation_applicable_f";;

(* First return value indicates if a model was found *)
(* Second return value is the optimized formula *)
(* Third argument indicates whether the encountered unsatisfied clause contains a conflict or not *)
(*let rec model_found assignment formula = 
    match formula with
        | Formula (Conjunction ([])) -> (true, formula, false) 
        | Formula (Conjunction (x :: xs)) -> (
                                              (* Formula optimization step: removes all satisfied clauses until first non-satisfied clause is encountered *)
                                              match (is_clause_satisfied assignment x) with 
                                                | true -> model_found assignment (Formula (Conjunction (xs)))
                                                | false -> (
                                                            match (unassigned_or_true assignment x) with
                                                                | [] -> (false, formula, true)
                                                                | [y] -> (false, Formula (Conjunction (y :: xs)), false)
                                                                | ys -> (false, Formula (Conjunction ((Disjunction (ys)) :: xs)), false)
                                                           )
                                             )
        | _ -> failwith "[Invalid argument] model_found";;*)

let model_found formula_opt = 
    match formula_opt with
        | Formula (Conjunction ([])) -> true
        | Formula (Conjunction (xs)) -> false
        | _ -> failwith "[Invalid argument] model_found: formula not in cnf";;

let rec find_conflict assignment formula =
    match formula with
        | Formula (Conjunction ([])) -> []
        | Formula (Conjunction (x :: xs)) -> (
                                              match (unassigned_or_true assignment x) with 
                                                | [] -> (* printf "CONFLICT: %s\n\n" (Printing.print_element x); *) [x]
                                                | y :: ys -> find_conflict assignment (Formula (Conjunction (xs)))   
                                             )
        (* Empty list in middle of conjunction possible? if so, another case is needed *)
        | _ -> failwith "[Invalid argument] find_conflict";;

let rec find_conflict_i assignment formula =
    match formula with
        | Formula (Conjunction ([])) -> []
        | Formula (Conjunction (x :: xs)) -> (
                                              match (unassigned_or_true_i assignment x) with 
                                                | [] ->  (*printf "CONFLICT: %s\n\n" (Printing.print_element x);*)  [x]
                                                | y :: ys -> find_conflict_i assignment (Formula (Conjunction (xs)))   
                                             )
        (* Empty list in middle of conjunction possible? if so, another case is needed *)
        | _ -> failwith "[Invalid argument] find_conflict";;

let rec find_conflict_i_map assignment assigned_map formula =
    match formula with
        | Formula (Conjunction ([])) -> []
        | Formula (Conjunction (x :: xs)) -> (
                                              match (unassigned_or_true_i_map assignment assigned_map x) with 
                                                | [] ->  (*printf "CONFLICT: %s\n\n" (Printing.print_element x);*)  [x]
                                                | y :: ys -> find_conflict_i_map assignment assigned_map (Formula (Conjunction (xs)))   
                                             )
        (* Empty list in middle of conjunction possible? if so, another case is needed *)
        | _ -> failwith "[Invalid argument] find_conflict";;

let conflict_exists assignment formula = 
    match (find_conflict assignment formula) with 
        | [] -> false
        | x :: xs -> true;;

let conflict_exists_i assignment formula = 
    match (find_conflict_i assignment formula) with 
        | [] -> false
        | x :: xs -> true;;

let conflict_exists_i_map assignment assigned_map formula = 
    match (find_conflict_i_map assignment assigned_map formula) with 
        | [] -> false
        | x :: xs -> true;;

let rec get_decision_literals_l assignment ls = 
    match assignment with 
        | Assignment ([]) -> ls
        | Assignment ((c, v, true, dl) :: xs) -> (get_decision_literals_l (Assignment xs) (ls @ [(c, v, true, dl)]))
        | Assignment ((c, v, false, dl) :: xs) -> (get_decision_literals_l (Assignment xs) ls);;

let get_decision_literals assignment = Assignment (get_decision_literals_l assignment []);;

let rec has_decision_literals assignment =
    match assignment with 
        | Assignment ([]) -> false
        | Assignment ((c, v, true, dl) :: xs) -> true
        | Assignment ((c, v, false, dl) :: xs) -> has_decision_literals (Assignment (xs));;

let is_proper_constraint cons = 
    match cons with 
    | Constraint (x) -> true
    | Index (x) -> true
    | AuxVar (x) -> false;;

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

(*let rec unit_propagation assignment formula formula_opt dl =
    match (formula, assignment) with 
        | (Formula (Conjunction ([])), Assignment ys) -> (assignment, Formula (Conjunction (formula_opt)))
        | (Formula (Conjunction ((Disjunction (x)) :: xs)), Assignment ys) -> ( 
                                                                                match (length x) with
                                                                                    | 1 -> (
                                                                                            match x with
                                                                                                | [Atom (y)] -> unit_propagation (Assignment (ys @ [(y, true, false, dl)])) (Formula (Conjunction (xs))) formula_opt dl
                                                                                                | [Not (Atom (y))] -> unit_propagation (Assignment (ys @ [(y, false, false, dl)])) (Formula (Conjunction (xs))) formula_opt dl
                                                                                                | _ -> failwith "[Invalid argument] unit_propagation"
                                                                                           )
                                                                                    | _ -> unit_propagation assignment (Formula (Conjunction (xs))) (formula_opt @ [Disjunction (x)]) dl
                                                                              )
        | (Formula (Conjunction ((Atom (x)) :: xs)), Assignment ys) ->  unit_propagation (Assignment (ys @ [(x, true, false, dl)])) (Formula (Conjunction (xs))) formula_opt dl
        | (Formula (Conjunction ((Not (Atom (x))) :: xs)), Assignment ys) ->  unit_propagation (Assignment (ys @ [(x, false, false, dl)])) (Formula (Conjunction (xs))) formula_opt dl
        | _ -> failwith "[Invaid argument] unit_propagation";; *)

let rec contains_literal lit_list literal = 
    match lit_list with
        | [] -> None
        | x :: xs -> (
                      match (x, literal) with
                        | (Atom (y), Atom (z)) -> (
                                                   match (compare y z) with 
                                                    | 0 -> Some (true)
                                                    | _ -> contains_literal xs literal
                                                  )
                        | (Not (Atom (y)), Not (Atom (z))) -> (
                                                               match (compare y z) with 
                                                                | 0 -> Some (true)
                                                                | _ -> contains_literal xs literal
                                                              )
                        | (Atom (y), Not (Atom (z))) -> (
                                                         match (compare y z) with
                                                            | 0 -> Some (false)
                                                            | _ -> contains_literal xs literal
                                                        )
                        | (Not (Atom (y)), Atom (z)) -> (
                                                         match (compare y z) with
                                                            | 0 -> Some (false)
                                                            | _ -> contains_literal xs literal
                                                        )
                        | _ -> failwith "[Invalid argument] contains_literal: literal list contains non-literal"
                     );;

let rec remove_literal clause literal acc =
    match clause with 
        | Disjunction ([]) -> Disjunction (acc)
        | Disjunction (x :: xs) -> (
                                    match (x, literal) with
                                        | (Atom (y), Atom (z)) -> remove_literal (Disjunction (xs)) literal (acc @ [x])
                                        | (Not (Atom (y)), Not (Atom (z))) -> remove_literal (Disjunction (xs)) literal (acc @ [x])
                                        | (Atom (y), Not (Atom (z))) -> (
                                                         match (compare y z) with
                                                            | 0 -> remove_literal (Disjunction (xs)) literal acc
                                                            | _ -> remove_literal (Disjunction (xs)) literal (acc @ [x])
                                                                        )
                                        | (Not (Atom (y)), Atom (z)) -> (
                                                         match (compare y z) with
                                                            | 0 -> remove_literal (Disjunction (xs)) literal acc
                                                            | _ -> remove_literal (Disjunction (xs)) literal (acc @ [x])
                                                                        )
                                        | _ -> failwith "[Invalid argument] remove_literal: argument not a literal"
                                   )
        | _ -> failwith "[Invalid argument] remove_literal: first argument not a clause";;

let rec propagate formula_opt literal acc next_lit conf = 
    match formula_opt with
        | (Formula (Conjunction ([]))) -> ((Formula (Conjunction (acc))), next_lit, conf)
        | (Formula (Conjunction ((Disjunction (x)) :: xs))) -> (
                                                                match (contains_literal x literal) with
                                                                    | Some (true) -> propagate (Formula (Conjunction (xs))) literal acc next_lit conf
                                                                    | Some (false) -> (
                                                                                       match (length x) with
                                                                                        | 1 -> ((Formula (Conjunction (acc))), next_lit, true)
                                                                                        | _ -> (
                                                                                                match (remove_literal (Disjunction (x)) literal []) with
                                                                                                | (Disjunction (y)) -> (
                                                                                                                        match (length y) with
                                                                                                                            | 1 -> propagate (Formula (Conjunction (xs))) literal (acc @ [Disjunction (y)]) y conf
                                                                                                                            | _ -> propagate (Formula (Conjunction (xs))) literal (acc @ [Disjunction (y)]) next_lit conf
                                                                                                                        )
                                                                                                | _ -> failwith "[Invalid argument] propagate: remove_literal did not return a clause"
                                                                                               )
                                                                                      )
                                                                    | None -> propagate (Formula (Conjunction (xs))) literal (acc @ [Disjunction (x)]) next_lit conf
                                                               )
        | (Formula (Conjunction (x :: xs))) -> (
                                                match (contains_literal [x] literal) with
                                                    | Some (true) -> propagate (Formula (Conjunction (xs))) literal acc next_lit conf
                                                    | Some (false) -> ((Formula (Conjunction (acc))), next_lit, true)
                                                    | None -> propagate (Formula (Conjunction (xs))) literal (acc @ [x]) next_lit conf
                                               )
        | _ -> failwith "[Invalid argument] propagate";;

let rec exhaustive_propagate assignment formula_opt literal dl =
    match (propagate formula_opt literal [] [] false) with
        | (f_new, next_lit, true) -> (
                                     let Assignment (xs) = assignment in match literal with
                                        | Atom (x) -> ((Assignment (xs @ [(x, true, false, dl)])), f_new, true)
                                        | Not (Atom (x)) -> ((Assignment (xs @ [(x, false, false, dl)])), f_new, true)
                                        | _ -> failwith "[Invalid argument] exhaustive_propagate: argument not a literal"
                                     )
        | (f_new, [], false) -> (
                                 let Assignment (xs) = assignment in match literal with
                                    | Atom (x) -> ((Assignment (xs @ [(x, true, false, dl)])), f_new, false)
                                    | Not (Atom (x)) -> ((Assignment (xs @ [(x, false, false, dl)])), f_new, false)
                                    | _ -> failwith "[Invalid argument] exhaustive_propagate: argument not a literal"
                                )
        | (f_new, next_lit, false) -> (
                                     let Assignment (xs) = assignment in match literal with
                                        | Atom (x) -> exhaustive_propagate (Assignment (xs @ [(x, true, false, dl)])) f_new (hd next_lit) dl
                                        | Not (Atom (x)) -> exhaustive_propagate (Assignment (xs @ [(x, false, false, dl)])) f_new (hd next_lit) dl
                                        | _ -> failwith "[Invalid argument] exhaustive_propagate: argument not a literal"
                                     );;

let rec unit_propagation assignment formula_it formula_opt dl = 
    match formula_it with 
        | (Formula (Conjunction ([]))) -> (assignment, formula_opt, false)
        | (Formula (Conjunction ((Disjunction (x)) :: xs))) -> (
                                                                match (length x) with
                                                                    | 1 -> exhaustive_propagate assignment formula_opt (hd x) dl
                                                                    | _ -> unit_propagation assignment (Formula (Conjunction (xs))) formula_opt dl
                                                               )
        | (Formula (Conjunction (x :: xs))) -> exhaustive_propagate assignment formula_opt x dl
        | _ -> failwith "[Invalid argument] unit_propagation: formula not in cnf";;

(*let rec exhaustive_unit_propagation assignment formula dl = 
    let (xs, f_opt) = (unit_propagation assignment formula [] dl) in 
        match (compare xs assignment) with 
            | 0 -> (xs, f_opt)
            | _ -> exhaustive_unit_propagation xs f_opt dl;;*)

let rec exhaustive_unit_propagation assignment formula_opt dl =
    let (xs, f_new, conf) = unit_propagation assignment formula_opt formula_opt dl in
        match (compare xs assignment) with
            | 0 -> (xs, f_new, conf)
            | _ -> (
                    match conf with
                    | false -> exhaustive_unit_propagation xs f_new dl
                    | true -> (xs, f_new, conf)
                   );;


(* Optimized to not include any 'is_assigned' call. This is only possible
   because model_found is always called first and removes false literals 
   from the first unsatisfied clause, leaving only unassigned literals
   in that clause *)
(* let rec decide assignment clause dl =
    match (clause, assignment) with
        | (Disjunction (x :: xs), Assignment ys) -> (
                                                     match x with
                                                        | Atom (y) -> (
                                                                       match is_proper_constraint y with
                                                                        | true -> (Assignment (ys @ [(y, true, true, dl + 1)]), (dl + 1), true)
                                                                        | false -> (Assignment (ys @ [(y, true, true, dl + 1)]), (dl + 1), false)
                                                                      )
                                                        | Not (Atom (y)) -> (
                                                                             match is_proper_constraint y with 
                                                                                | true -> (Assignment (ys @ [(y, false, true, dl + 1)]), (dl + 1), true)
                                                                                | false -> (Assignment (ys @ [(y, false, true, dl + 1)]), (dl + 1), false)
                                                                            )
                                                        | _ -> failwith "[Invalid argument] decide: formula not in CNF"
                                                    )
        | _ -> failwith "[Invalid argument] decide";; *)

(* let rec decision assignment formula dl = 
    match formula with
        | Formula (Conjunction ([])) -> (assignment, dl, false)
        | Formula (Conjunction (x :: xs)) -> decide assignment x dl
        | _ -> failwith "[Invalid argument] decision";; *)

let rec decision assignment formula_opt dl = 
    match formula_opt with 
        | (Formula (Conjunction ([]))) -> failwith "[Invalid argument] empty formula"
        | (Formula (Conjunction ((Disjunction (x)) :: xs))) -> (
                                                                match (length x) with
                                                                    | 1 -> exhaustive_propagate assignment formula_opt (hd x) dl
                                                                    | _ -> let (Assignment (ys)) = assignment in let (f_new, next_lit, conf) = propagate formula_opt (hd x) [] [] false in
                                                                           (
                                                                            match (hd x) with 
                                                                                | Atom (y) -> ((Assignment (ys @ [(y, true, true, dl + 1)])), f_new, conf)
                                                                                | Not (Atom (y)) -> ((Assignment (ys @ [(y, false, true, dl + 1)])), f_new, conf)
                                                                                | _ -> failwith "[Invalid argument] decision: formula not in CNF"
                                                                           )
                                                               )
        | _ -> failwith "[Invalid argument] formula not in cnf";;    

let learn formula clause =
    match clause with 
     | Disjunction ([]) -> formula 
     | Disjunction ([x]) -> formula
     | Disjunction (xs) -> (
                            match formula with
                                | Formula (Conjunction (ys)) -> if mem clause ys 
                                                                then formula
                                                                else Formula (Conjunction ([clause] @ ys))
                                | _ -> failwith "[Invalid argument] learn: formula not in CNF"
                           )
    | _ -> failwith "[Invalid argument] learn: second argument not a clause";;

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
                     );;
                
let rec is_still_conflict_i (assignment : (constraint_n * bool * bool * int) list) formula clause =
    match assignment with
        | [] -> false 
        | x :: xs -> (
                      match (unassigned_or_true_i (Assignment (assignment)) clause) with
                        | [] -> true 
                        | y :: ys -> false
                     );;

let rec find_minimal_i_l (assignment : (constraint_n * bool * bool * int) list) formula clause ls =
    match (is_still_conflict ls formula clause) with
        | true -> ls
        | false -> find_minimal_i_l (tl assignment) formula clause (ls @ [(hd assignment)]);;

let find_minimal_i (assignment : (constraint_n * bool * bool * int) list) formula clause = find_minimal_i_l assignment formula clause [];;

let rec find_minimal_i_l_indexed (assignment : (constraint_n * bool * bool * int) list) formula clause ls =
    match (is_still_conflict_i ls formula clause) with
        | true -> ls
        | false -> find_minimal_i_l_indexed (tl assignment) formula clause (ls @ [(hd assignment)]);;

let find_minimal_i_indexed (assignment : (constraint_n * bool * bool * int) list) formula clause = find_minimal_i_l_indexed assignment formula clause [];;

let rec transform_to_neg_clause assignment =
    match assignment with 
        | Assignment ([]) -> []
        | Assignment ((c, true, d, dl) :: xs) -> [Not (Atom c)] @ (transform_to_neg_clause (Assignment xs))
        | Assignment ((c, false, d, dl) :: xs) -> [Atom c] @ (transform_to_neg_clause (Assignment xs));;

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
    | (c, v, d, dl) -> get_last_dl_literals_rec assignment dl;;

let rec find_backjump_clause_l (assignment : (constraint_n * bool * bool * int) list) formula clause ls = 
    match (is_still_conflict (ls @ (get_last_dl_literals assignment)) formula clause) with 
        | true -> ls @ (get_last_dl_literals assignment)
        | false -> find_backjump_clause_l (tl assignment) formula clause (ls @ [(hd assignment)]);;

let find_backjump_clause (assignment : (constraint_n * bool * bool * int) list) formula clause = Disjunction (transform_to_neg_clause (get_decision_literals (Assignment (find_backjump_clause_l (find_minimal_i assignment formula clause) formula clause []))));;
        
let rec find_backjump_clause_l_i (assignment : (constraint_n * bool * bool * int) list) formula clause ls = 
    match (is_still_conflict_i (ls @ (get_last_dl_literals assignment)) formula clause) with 
        | true -> ls @ (get_last_dl_literals assignment)
        | false -> find_backjump_clause_l_i (tl assignment) formula clause (ls @ [(hd assignment)]);;

(* Get target decision level for backjumping. *)
(* Relies on increasing order of decision levels in the assignment *)
let rec get_decision_level (assignment : (constraint_n * bool * bool * int) list) literal = 
    match assignment with
    | [] -> failwith "[Invalid argument] get_decision_level: literal not in assignment list"
    | x :: xs -> (
                  match (x) with
                    | (c, v, d, dl) -> (
                                        match literal with 
                                            | Atom (y) -> (
                                                           match (compare c y) with 
                                                            | 0 -> dl
                                                            | _ -> get_decision_level xs literal
                                                          )
                                            | Not (Atom (y)) -> (
                                                                 match (compare c y) with 
                                                                    | 0 -> dl
                                                                    | _ -> get_decision_level xs literal
                                                                )
                                            | _ -> failwith "[Invalid argument] get_decision_level: argument not a literal"
                                       )
                 );;

let rec get_decision_level_i (assignment : (constraint_n * bool * bool * int) list) literal = 
    match assignment with
    | [] -> failwith "[Invalid argument] get_decision_level: literal not in assignment list"
    | x :: xs -> (
                  match (x) with
                    | (Index (i1), v, d, dl) -> (
                                        match literal with 
                                            | Atom (Index (i2)) -> (
                                                                    match (compare i1 i2) with 
                                                                        | 0 -> dl
                                                                        | _ -> get_decision_level_i xs literal
                                                                   )
                                            | Not (Atom (Index (i2))) -> (
                                                                          match (compare i1 i2) with 
                                                                            | 0 -> dl
                                                                            | _ -> get_decision_level_i xs literal
                                                                         )
                                            | Atom (AuxVar (_)) -> get_decision_level_i xs literal
                                            | Not (Atom (AuxVar (_))) -> get_decision_level_i xs literal
                                            | _ -> failwith "[Invalid argument] get_decision_level_i: argument not a literal or not in index representation"
                                       )
                    | (AuxVar (i1), v, d, dl) -> (
                                                  match literal with
                                                    | Atom (AuxVar (i2)) -> (
                                                                    match (compare i1 i2) with 
                                                                        | 0 -> dl
                                                                        | _ -> get_decision_level_i xs literal
                                                                   )
                                                    | Not (Atom (AuxVar (i2))) -> (
                                                                          match (compare i1 i2) with 
                                                                            | 0 -> dl
                                                                            | _ -> get_decision_level_i xs literal
                                                                         )
                                                    | Atom (Index (_)) -> get_decision_level_i xs literal
                                                    | Not (Atom (Index (_))) -> get_decision_level_i xs literal
                                                 )
                    | _ -> failwith "[Invalid argument] get_decision_level_i: Indexed variant used with non-index representation"
                 );;

let rec clauselist_to_neg_clause_rec clauses result = 
    match clauses with
        | [] -> Disjunction (result)
        | (Atom (x)) :: xs -> clauselist_to_neg_clause_rec xs (result @ [(Not (Atom (x)))])
        | (Not (Atom (x))) :: xs -> clauselist_to_neg_clause_rec xs (result @ [(Atom (x))])
        | _ -> failwith "[Invalid argument] clauselist_to_neg_clause_rec: argument not a list of literals";;

let clauselist_to_neg_clause clauses = 
    match clauses with 
     | [] -> failwith "[Invalid argument] clauselist_to_neg_clause: clause empty"
     | xs -> clauselist_to_neg_clause_rec clauses [];;

(* assignment is the reverse of the actual Assignment so we are starting from the last assigned literal and going back *)
let rec get_last_decision_literal assignment =
    match assignment with 
        | Assignment ([]) -> failwith "[Invalid argument] get_last_decision_literal: assignment contains no decisions"
        | Assignment ((c, v, d, l) :: xs) -> if d = true 
                                             then (
                                                   match v with 
                                                    | true -> Not (Atom (c))
                                                    | false -> Atom (c)
                                                  )
                                             else get_last_decision_literal (Assignment (xs));; 

let rec get_current_level_literals_rec assignment clause dl result =
    let Assignment (xs) = assignment in 
        match clause with
            | Disjunction ([]) -> result
            | Disjunction (y :: ys) -> if (get_decision_level_i xs y) = dl
                                       then get_current_level_literals_rec assignment (Disjunction (ys)) dl (result @ [y])
                                       else get_current_level_literals_rec assignment (Disjunction (ys)) dl result;;

let get_current_level_literals assignment clause dl = get_current_level_literals_rec assignment clause dl [];;

let rec transform_to_bj_clause assignment clause dl last_level_literals result =
    let Assignment (xs) = assignment in 
        match clause with 
            | Disjunction ([]) -> result @ last_level_literals
            | Disjunction (y :: ys) -> if (get_decision_level_i xs y) = dl 
                                       then transform_to_bj_clause assignment (Disjunction (ys)) dl last_level_literals result
                                       else transform_to_bj_clause assignment (Disjunction (ys)) dl last_level_literals (result @ [y]);;

let find_backjump_clause_i_new assignment clause dl = let Assignment (xs) = assignment in
                                     Disjunction (transform_to_bj_clause assignment clause dl [(get_last_decision_literal (Assignment (rev xs)))] []);;

let find_backjump_clause_i (assignment : (constraint_n * bool * bool * int) list) formula clause = Disjunction (transform_to_neg_clause (Assignment (find_backjump_clause_l_i (find_minimal_i_indexed assignment formula clause) formula clause [])));;

let get_current_decision_level assignment = 
    match assignment with 
        | Assignment ([]) -> failwith "[Invalid argument] get_current_decision_level"
        | Assignment (xs) -> (
                              match (hd (rev xs)) with
                                | (c, v, d, dl) -> dl 
                             );;

(* Backjump *)
let rec backjump_rec assignment dl clause ls = 
    match assignment with
        | Assignment ([]) -> failwith "[Invalid argument] backjump_rec: empty assignment"
        | Assignment ((c, v, d, l) :: xs) -> (
                                              match (compare l dl) with
                                                | 1 -> ( 
                                                        match clause with
                                                            | Disjunction ([]) -> (
                                                                                   match v with 
                                                                                    | true -> ls @ [(c, false, false, dl)]
                                                                                    | false -> ls @ [(c, true, false, dl)]
                                                                                  )
                                                            | Disjunction (ys) -> (
                                                                                   match (hd (rev ys)) with
                                                                                    | Atom (y) -> ls @ [(y, true, false, dl)]
                                                                                    | Not (Atom (y)) -> ls @ [(y, false, false, dl)]
                                                                                    | _ -> failwith "[Invalid argument] backjump_rec: last element of disjunction not a literal"
                                                                                  )
                                                            | _ -> failwith "[Invalid argument] backjump_rec: clause not a disjunction"
                                                       )
                                                | 0 -> backjump_rec (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | -1 -> backjump_rec (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | _ -> failwith "[Invalid argument] backjump_rec"
                                             );;

let rec backjump_rec_twl assignment dl clause ls = 
    match assignment with
        | Assignment ([]) -> failwith "[Invalid argument] backjump_rec: empty assignment"
        | Assignment ((c, v, d, l) :: xs) -> (
                                              match (compare l dl) with
                                                | 1 -> ( 
                                                        match clause with
                                                            | Disjunction ([]) -> (
                                                                                   match v with 
                                                                                    | true -> (ls @ [(c, false, false, dl)], Atom (c))
                                                                                    | false -> (ls @ [(c, true, false, dl)], Not (Atom (c)))
                                                                                  )
                                                            | Disjunction (ys) -> (
                                                                                   match (hd (rev ys)) with
                                                                                    | Atom (y) -> (ls @ [(y, true, false, dl)], Not (Atom (y)))
                                                                                    | Not (Atom (y)) -> (ls @ [(y, false, false, dl)], Atom (y))
                                                                                    | _ -> failwith "[Invalid argument] backjump_rec: last element of disjunction not a literal"
                                                                                  )
                                                            | _ -> failwith "[Invalid argument] backjump_rec: clause not a disjunction"
                                                       )
                                                | 0 -> backjump_rec_twl (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | -1 -> backjump_rec_twl (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | _ -> failwith "[Invalid argument] backjump_rec"
                                             );;

let backjump assignment formula = 
    (*printf "BACKJUMP\n\n";*) match assignment with 
        | Assignment (xs) -> let ys = (find_conflict assignment formula) in
                                (
                                 match (find_backjump_clause xs formula (hd ys)) with
                                  | Disjunction (zs) -> (
                                                        match (length zs) with 
                                                            | 0 -> (Assignment (backjump_rec assignment
                                                                                            0
                                                                                            (Disjunction (zs))
                                                                                            []),
                                                                    Disjunction (zs))
                                                            | 1 -> (Assignment (backjump_rec assignment
                                                                                            0
                                                                                            (Disjunction (zs))
                                                                                            []),
                                                                    Disjunction (zs))
                                                            | _ ->  (Assignment (backjump_rec assignment
                                                                                (get_decision_level xs (hd (tl (rev zs)))) 
                                                                                (Disjunction (zs))
                                                                                []),
                                                                    Disjunction (zs))
                                                        )
                                  | _ -> failwith "[Invalid argument] backjump: find_backjump_clause did not return a clause"
                                );;

let rec backtrack_rec assignment dl ls =
    match assignment with
        | Assignment ([]) -> failwith "[Invalid argument] backtrack: assignment list does not contain literals of current decision level"
        | Assignment ((c, v, d, l) :: xs) -> (
                                              match (compare dl l) with
                                                | 0 -> (
                                                        match (v, d) with
                                                            | (true, true) -> ls @ [(c, false, false, (l - 1))]
                                                            | (false, true) -> ls @ [(c, true, false, (l - 1))]
                                                            | (_, false) -> failwith "[Invalid argument] backtrack: assignment list does not contain a decision literal of current decision level"
                                                       )
                                                | _ -> backtrack_rec (Assignment (xs)) dl (ls @ [(c, v, d, l)])
                                             );;

let backtrack assignment dl = Assignment (backtrack_rec assignment dl []);;

(* The actual DPLL procedure *)

(* 'formula' is the actual initial formula and never changes. *)
(* 'formula_opt' is an optimized alternative formula where every *)
(* satisfied clause has been removed to make most of the function *)
(* calls in the procedure more efficient *)
(*let rec dpll_rec assignment formula formula_opt dl = 
    match (model_found assignment formula_opt) with
        | (true, _, _) -> (
                           match (Util.to_simplex_format_init assignment) with 
                            | (sf_assignment, cs) -> ( 
                                                      match Simplex.simplex sf_assignment with
                                                        | Some (x) -> true
                                                        | None -> restart (learn formula (Disjunction (transform_to_neg_clause cs)))
                                                     )
                           )
        | (false, formula_new, false) -> (
                                          let (xs, f_opt) = (exhaustive_unit_propagation assignment formula_new dl) in 
                                                 match (compare assignment xs) with
                                                    | 0 -> (
                                                            match (decision assignment formula_new dl) with
                                                                | (ys, l, _) -> dpll_rec ys formula formula_new l
                                                           )
                                                    | _ -> dpll_rec xs formula f_opt dl
                                         )
        | (false, formula_new, true) -> ( 
                                         match (has_decision_literals assignment) with 
                                            | false -> false
                                            | true -> let (xs, bj_clause) = (backjump assignment formula) in let formula_l = (learn formula bj_clause) in dpll_rec xs formula_l formula_l (get_current_decision_level xs)
                                        )
                                   (*match (conflict_exists assignment formula_new) with
                                    | true -> ( 
                                               match (has_decision_literals assignment) with 
                                                | false -> false
                                                | true -> let xs = (backjump assignment formula) in dpll_rec xs formula formula (get_current_decision_level xs)
                                              )
                                    | false -> (
                                                (*match (unit_propagation_applicable_f assignment formula_new) with 
                                                    | true -> let xs = (exhaustive_unit_propagation assignment formula_new dl) in dpll_rec xs formula formula_new dl
                                                    | false -> (
                                                                match (decision assignment formula_new dl) with
                                                                    | (ys, l) -> dpll_rec ys formula formula_new l
                                                               )*)
                                                let (xs, f_opt) = (exhaustive_unit_propagation assignment formula_new dl) in 
                                                 match (compare assignment xs) with
                                                    | 0 -> (
                                                            match (decision assignment formula_new dl) with
                                                                | (ys, l) -> dpll_rec ys formula formula_new l
                                                           )
                                                    | _ -> dpll_rec xs formula f_opt dl
                                               )
                                  );;*) *)

(* and dpll formula = dpll_rec (unit (Assignment ([])) formula) formula formula 0 *)

let rec dpll_rec assignment formula formula_opt dl =
    (*Printing.print_assignment assignment; printf "\n\n";*) match (model_found formula_opt) with
    | true -> (
               match (Util.to_simplex_format_init assignment) with 
                            | (sf_assignment, cs) -> ( 
                                                      match Simplex.simplex sf_assignment with
                                                        | Some (x) -> true
                                                        | None -> restart (learn formula (Disjunction (transform_to_neg_clause cs)))
                                                     )
              )
    | false -> (
                let (xs, f_new, conf) = (unit_propagation assignment formula_opt formula_opt dl) in 
                    match conf with 
                        | true -> ( 
                                   match (has_decision_literals xs) with 
                                    | false -> false
                                    | true -> let (ys, bj_clause) = (backjump xs formula) in 
                                        (
                                         match bj_clause with 
                                            | Disjunction ([]) -> dpll_rec ys formula formula (get_current_decision_level ys)
                                            | Disjunction (zs) -> let formula_l = (learn formula bj_clause) in dpll_rec ys formula_l formula_l (get_current_decision_level ys)
                                            | _ -> failwith "[Invalid argument] dpll_rec: backjump clause not a clause"
                                        )
                                  )
                        | false -> (
                                    match (compare assignment xs) with
                                        | 0 -> (
                                                match (decision assignment f_new dl) with
                                                    | (ys, f_new_d, false) -> dpll_rec ys formula f_new_d (dl + 1)
                                                    | (ys, _, true) -> ( 
                                                                        let (zs, bj_clause) = (backjump ys formula) in 
                                                                        (
                                                                         match bj_clause with
                                                                            | Disjunction ([]) -> dpll_rec ys formula formula (get_current_decision_level ys)
                                                                            | Disjunction (ws) -> let formula_l = (learn formula bj_clause) in dpll_rec ys formula_l formula_l (get_current_decision_level zs)
                                                                            | _ -> failwith "[Invalid argument] dpll_rec: backjump clause not a clause"
                                                                        )
                                                                       )
                                               )
                                        | _ -> dpll_rec xs formula f_new dl
                                   )
               )

and dpll formula = (*printf "FORMULA: "; Printing.print_formula formula; printf "\n\n";*) dpll_rec (Assignment ([])) formula formula 0

and restart formula = dpll formula;;

let rec dpll_inc_rec assignment formula formula_opt dl =
    (*Printing.print_assignment assignment; printf "\n\n";*) match (model_found formula_opt) with
    | true -> (
               match (Util.to_simplex_format_init assignment) with 
                            | (sf_assignment, cs) -> ( 
                                                      match Simplex.simplex sf_assignment with
                                                        | Some (x) -> true
                                                        | None -> restart_inc (learn formula (Disjunction (transform_to_neg_clause cs)))
                                                     )
              )
    | false -> (
                let (xs, f_new, conf) = (unit_propagation assignment formula_opt formula_opt dl) in 
                    match conf with 
                        | true -> ( 
                                   match (has_decision_literals xs) with 
                                    | false -> false
                                    | true -> let (ys, bj_clause) = (backjump xs formula) in 
                                        (
                                         match bj_clause with 
                                            | Disjunction ([]) -> dpll_inc_rec ys formula formula (get_current_decision_level ys)
                                            | Disjunction (zs) -> let formula_l = (learn formula bj_clause) in dpll_inc_rec ys formula_l formula_l (get_current_decision_level ys)
                                            | _ -> failwith "[Invalid argument] dpll_inc_rec: backjump clause not a clause"
                                        )
                                  )
                        | false -> (
                                    match (compare assignment xs) with
                                        | 0 -> (
                                                match (Util.to_simplex_format_init assignment) with 
                                                                | (sf_assignment, cs) -> ( 
                                                                                        match Simplex.simplex sf_assignment with
                                                                                            | Some (x) -> (
                                                                                                            match (decision assignment f_new dl) with
                                                                                                                | (ys, f_new_d, false) -> dpll_inc_rec ys formula f_new_d (dl + 1)
                                                                                                                | (ys, _, true) -> ( 
                                                                                                                                    let (zs, bj_clause) = (backjump ys formula) in 
                                                                                                                                    (
                                                                                                                                    match bj_clause with
                                                                                                                                        | Disjunction ([]) -> dpll_inc_rec ys formula formula (get_current_decision_level ys)
                                                                                                                                        | Disjunction (ws) -> let formula_l = (learn formula bj_clause) in dpll_inc_rec ys formula_l formula_l (get_current_decision_level zs)
                                                                                                                                        | _ -> failwith "[Invalid argument] dpll_inc_rec: backjump clause not a clause"
                                                                                                                                    )
                                                                                                                                )
                                                                                                        )
                                                                                            | None -> restart_inc (learn formula (Disjunction (transform_to_neg_clause cs)))
                                                                                        )
                                                )
                                        | _ -> dpll_inc_rec xs formula f_new dl
                                   )
               )

and dpll_inc formula = (*printf "FORMULA: "; Printing.print_formula formula; printf "\n\n";*) dpll_inc_rec (Assignment ([])) formula formula 0

and restart_inc formula = dpll_inc formula;;

(**********************************************)
(* Two-watched-literal implementation of DPLL *)
(**********************************************)

let rec model_found_twl assignment formula = 
    match formula with
        | Formula (Conjunction ([])) -> true
        | Formula (Conjunction (x :: xs)) -> (
                                              match is_clause_satisfied assignment x with
                                                | true -> model_found_twl assignment (Formula (Conjunction (xs)))
                                                | false -> false
                                             )
        | _ -> failwith "[Invalid argument] model_found_twl: formula not in CNF";;

let rec model_found_twl_i assignment formula = 
    match formula with
        | Formula (Conjunction ([])) -> true
        | Formula (Conjunction (x :: xs)) -> (
                                              match is_clause_satisfied_i assignment x with
                                                | true -> model_found_twl_i assignment (Formula (Conjunction (xs)))
                                                | false -> false
                                             )
        | _ -> failwith "[Invalid argument] model_found_twl: formula not in CNF";;

let rec check_clause assignment f_map clause literal prop conf = 
    match clause with
        | Disjunction (w1 :: w2 :: ws) -> (
                                           match (compare w1 literal) with
                                            | 0 -> if is_true assignment w2 
                                                   then (f_map, prop, conf)
                                                   else (
                                                         if is_assigned assignment w2 
                                                         then (
                                                               if is_clause_satisfied assignment clause
                                                               then (f_map, prop, conf)
                                                               else (
                                                                     match (unassigned_or_true assignment (Disjunction (ws))) with
                                                                        | [] -> (f_map, prop, [clause])
                                                                        | x :: xs -> (TWL_Map.add (Printing.print_element w1) 
                                                                                           (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                           (TWL_Map.add (Printing.print_element w2) 
                                                                                                        (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                     ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                     (TWL_Map.add (Printing.print_element w2) 
                                                                                                                                  ((TWL_Map.find (Printing.print_element w2) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                                                 f_map))),
                                                                                    prop, 
                                                                                    conf)
                                                                    )
                                                              )
                                                         else (
                                                               match (unassigned_or_true assignment (Disjunction (ws))) with
                                                                | [] -> (f_map, [w2], conf)
                                                                | x :: xs ->  (TWL_Map.add (Printing.print_element w1) 
                                                                                           (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                           (TWL_Map.add (Printing.print_element w2) 
                                                                                                        (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                     ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                     (TWL_Map.add (Printing.print_element w2) 
                                                                                                                                  ((TWL_Map.find (Printing.print_element w2) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                                  f_map))),
                                                                              prop, 
                                                                              conf)
                                                              )
                                                        )
                                            | _ -> (
                                                    match (compare w2 literal) with
                                                     | 0 -> if is_true assignment w1 
                                                            then (f_map, prop, conf)
                                                            else (
                                                                    if is_assigned assignment w1 
                                                                    then (
                                                                          if is_clause_satisfied assignment clause 
                                                                          then (f_map, prop, conf)
                                                                          else (
                                                                                match (unassigned_or_true assignment (Disjunction (ws))) with
                                                                                    | [] -> (f_map, prop, [clause])
                                                                                    | x :: xs -> (TWL_Map.add (Printing.print_element w1) 
                                                                                                            (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                                            (TWL_Map.add (Printing.print_element w2) 
                                                                                                                        (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                                        ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                                        (TWL_Map.add (Printing.print_element w1) 
                                                                                                                                                    ((TWL_Map.find (Printing.print_element w2) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                                                                    f_map))),
                                                                                                prop, 
                                                                                                conf)
                                                                               )
                                                                         )
                                                                    else (
                                                                        match (unassigned_or_true assignment (Disjunction (ws))) with
                                                                            | [] -> (f_map, [w1], conf)
                                                                            | x :: xs -> (TWL_Map.add (Printing.print_element w1) 
                                                                                                      (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                                      (TWL_Map.add (Printing.print_element w2) 
                                                                                                                   (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                                                   (TWL_Map.add (Printing.print_element x) 
                                                                                                                                ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                                (TWL_Map.add (Printing.print_element w1) 
                                                                                                                                             ((TWL_Map.find (Printing.print_element w2) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                                                            f_map))),
                                                                                         prop, 
                                                                                         conf)
                                                                        )
                                                                    )
                                                     | _ -> failwith "[Invalid argument] check_clause: clause in wrong watch list"
                                                   )
                                          )
        | _ -> failwith "[Invalid argument] check_clause";;

let check_clause_i assignment assigned_map f_map clause literal prop conf = 
    (*Printing.print_assignment assignment; printf "\n\n";*) match clause with
        | Disjunction (w1 :: w2 :: ws) -> (*
                                           match (compare w1 literal) with
                                            | 0 -> if is_true_i assignment w2 
                                                   then (f_map, prop, conf)
                                                   else (
                                                         if is_assigned_i assignment w2 
                                                         then (
                                                               if is_clause_satisfied_i assignment clause 
                                                               then (f_map, prop, conf)
                                                               else (
                                                                     match (unassigned_or_true_i assignment (Disjunction (ws))) with
                                                                        | [] -> (f_map, prop, [clause])
                                                                        | x :: xs -> (TWL_Map.add (Printing.print_element w1) 
                                                                                           (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                           (TWL_Map.add (Printing.print_element w2) 
                                                                                                        ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map)) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                     ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                     f_map)),
                                                                                    prop, 
                                                                                    conf)
                                                                    )
                                                              )
                                                         else (
                                                               match (unassigned_or_true_i assignment (Disjunction (ws))) with
                                                                | [] -> (f_map, [w2], conf)
                                                                | x :: xs -> (TWL_Map.add (Printing.print_element w1) 
                                                                                           (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                           (TWL_Map.add (Printing.print_element w2) 
                                                                                                        ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map)) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                     ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                     f_map)),
                                                                             prop, 
                                                                             conf)
                                                              )
                                                        )
                                            | _ -> (
                                                    match (compare w2 literal) with
                                                     | 0 -> if is_true_i assignment w1 
                                                            then (f_map, prop, conf)
                                                            else (
                                                                    if is_assigned_i assignment w1 
                                                                    then (
                                                                          if is_clause_satisfied_i assignment clause 
                                                                          then (f_map, prop, conf)
                                                                          else (
                                                                                match (unassigned_or_true_i assignment (Disjunction (ws))) with
                                                                                    | [] -> (f_map, prop, [clause])
                                                                                    | x :: xs -> (TWL_Map.add (Printing.print_element w2) 
                                                                                           (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                           (TWL_Map.add (Printing.print_element w1) 
                                                                                                        ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map)) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                     ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                     f_map)),
                                                                                            prop, 
                                                                                            conf)
                                                                                )
                                                                         )
                                                                    else (
                                                                        match (unassigned_or_true_i assignment (Disjunction (ws))) with
                                                                            | [] -> (f_map, [w1], conf)
                                                                            | x :: xs -> (TWL_Map.add (Printing.print_element w2) 
                                                                                           (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                           (TWL_Map.add (Printing.print_element w1) 
                                                                                                        ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map)) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                        (TWL_Map.add (Printing.print_element x) 
                                                                                                                     ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                     f_map)),
                                                                                            prop, 
                                                                                            conf)
                                                                        )
                                                                    )
                                                     | _ -> failwith "[Invalid argument] check_clause_i: clause in wrong watch list"
                                                   )
                                          *)
                                          (
                                           if is_clause_satisfied_i_map assignment assigned_map clause 
                                           then (f_map, prop, conf)
                                           else ( 
                                            match (compare w1 literal) with
                                                | 0 ->  ( if is_assigned_i_map assignment assigned_map w2 
                                                            then (
                                                                 (* if is_true_i assignment w2 
                                                                  then (f_map, prop, conf)
                                                                  else ( *)
                                                                        match (get_first_unassigned_var_map assignment assigned_map (Disjunction (ws))) with
                                                                            | [] -> (f_map, prop, [clause])
                                                                            | [x] -> (TWL_Map.add (Printing.print_element w1) 
                                                                                            (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                            (TWL_Map.add (Printing.print_element w2) 
                                                                                                            ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map)) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                            (TWL_Map.add (Printing.print_element x) 
                                                                                                                        ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                        f_map)),
                                                                                        [(x, clause)], 
                                                                                        conf)
                                                                        )
                                                                (*)*)
                                                            else (
                                                                match (get_first_unassigned_var_map assignment assigned_map (Disjunction (ws))) with
                                                                    | [] -> (f_map, [(w2, clause)], conf)
                                                                    | [x] -> (TWL_Map.add (Printing.print_element w1) 
                                                                                            (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map))
                                                                                            (TWL_Map.add (Printing.print_element w2) 
                                                                                                            ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map)) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                            (TWL_Map.add (Printing.print_element x) 
                                                                                                                        ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w2 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w1]))))])
                                                                                                                        f_map)),
                                                                                prop, 
                                                                                conf)
                                                                )
                                                            )
                                                | _ -> (
                                                        match (compare w2 literal) with
                                                        | 0 -> ( if is_assigned_i_map assignment assigned_map w1 
                                                                        then (
                                                                              (*if is_true_i assignment w1 
                                                                              then (f_map, prop, conf)
                                                                              else ( *)
                                                                                    match (get_first_unassigned_var_map assignment assigned_map (Disjunction (ws))) with
                                                                                        | [] -> (f_map, prop, [clause])
                                                                                        | [x] -> (TWL_Map.add (Printing.print_element w2) 
                                                                                            (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                            (TWL_Map.add (Printing.print_element w1) 
                                                                                                            ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map)) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                            (TWL_Map.add (Printing.print_element x) 
                                                                                                                        ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                        f_map)),
                                                                                                [(x, clause)], 
                                                                                                conf)
                                                                                (*)*)
                                                                            )
                                                                        else (
                                                                            match (get_first_unassigned_var_map assignment assigned_map (Disjunction (ws))) with
                                                                                | [] -> (f_map, [(w1, clause)], conf)
                                                                                | [x] -> (TWL_Map.add (Printing.print_element w2) 
                                                                                            (filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w2) f_map))
                                                                                            (TWL_Map.add (Printing.print_element w1) 
                                                                                                            ((filter (fun c -> (compare c clause) <> 0) (TWL_Map.find (Printing.print_element w1) f_map)) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                            (TWL_Map.add (Printing.print_element x) 
                                                                                                                        ((TWL_Map.find (Printing.print_element x) f_map) @ [(Disjunction (x :: w1 :: (filter (fun l -> (compare l x) <> 0) (ws @ [w2]))))])
                                                                                                                        f_map)),
                                                                                                prop, 
                                                                                                conf)
                                                                            )
                                                                        )
                                                        | _ -> failwith "[Invalid argument] check_clause_i: clause in wrong watch list"
                                                    )
                                            )
                                          )
        | _ -> failwith "[Invalid argument] check_clause_i";;

let rec update_clauses assignment f_map clauses literal prop conf = 
    match clauses with
        | [] -> (f_map, prop, conf)
        | x :: xs -> let (new_map, new_prop, new_conf) = (check_clause assignment f_map x literal prop conf) in 
                        update_clauses assignment new_map xs literal new_prop new_conf;;

let rec update_clauses_i assignment assigned_map f_map clauses literal prop conf = 
    (*printf "updating clauses: %s\n\n" (Printing.print_element_list clauses);*) match clauses with
        | [] -> (f_map, prop, conf)
        | x :: xs -> let (new_map, new_prop, new_conf) = (check_clause_i assignment assigned_map f_map x literal prop conf) in 
                        update_clauses_i assignment assigned_map new_map xs literal new_prop new_conf;;

(* NOTE: literal should always be the negation of the literal that was just assigned *)
(*       This function then updates the watch list of the negated literal *)
let update_watch_lists assignment f_map literal = update_clauses assignment f_map (TWL_Map.find (Printing.print_element literal) f_map) literal [] [];;

let update_watch_lists_i assignment assigned_map f_map literal = update_clauses_i assignment assigned_map f_map (TWL_Map.find (Printing.print_element literal) f_map) literal [] [];;

let rec update_watch_lists_l_rec assignment f_map l_list prop conf =
    match l_list with
        | [] -> (f_map, prop, conf)
        | x :: xs -> let (f_map_new, prop_new, conf_new) = update_watch_lists assignment f_map x in
                        update_watch_lists_l_rec assignment f_map_new xs prop_new conf_new;;

let update_watch_lists_l assignment f_map l_list = update_watch_lists_l_rec assignment f_map l_list [] [];;

let rec update_watch_lists_i_l_rec assignment assigned_map f_map l_list prop conf =
    match l_list with
        | [] -> (f_map, prop, conf)
        | x :: xs -> let (f_map_new, prop_new, conf_new) = update_watch_lists_i assignment assigned_map f_map x in
                        update_watch_lists_i_l_rec assignment assigned_map f_map_new xs prop_new conf_new;;

let update_watch_lists_i_l assignment assigned_map f_map l_list = update_watch_lists_i_l_rec assignment assigned_map f_map l_list [] [];;

let rec choose_decision_literal assignment clause = 
    match clause with
        | Disjunction ([]) -> failwith "[Invalid argument] choose_decision_literal: clause does not contain a literal suited for decision"
        | Disjunction (x :: xs) -> if is_assigned assignment x 
                                   then choose_decision_literal assignment (Disjunction (xs))
                                   else x
        | _ -> failwith "[Invalid argument] choose_decision_literal: argument not a clause";;

let rec choose_decision_literal_i assignment clause = 
    (*if is_clause_satisfied_i assignment clause 
    then []
    else*) (
         match clause with
            | Disjunction ([]) -> []
            | Disjunction (x :: xs) -> if is_assigned_i assignment x 
                                       then choose_decision_literal_i assignment (Disjunction (xs))
                                       else [x]
            | _ -> failwith "[Invalid argument] choose_decision_literal: argument not a clause"
        );;

let rec decision_twl formula assignment f_map dl =
    match formula with
     | Formula (Conjunction (cs)) -> (
                                    match contains_unassigned_literal assignment (hd cs) with
                                        | false -> decision_twl (Formula (Conjunction (tl cs))) assignment f_map dl
                                        | true -> (
                                                    let Assignment (xs) = assignment in
                                                    match choose_decision_literal assignment (hd cs) with
                                                        | Atom (x) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Not (Atom (x))) in 
                                                                        (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, prop, conf)
                                                        | Not (Atom (x)) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Atom (x)) in
                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, prop, conf) 
                                                        | _ -> failwith "[Invalid argument] decision_twl: choose_decision_literal did not return a literal"
                                                )
                                    )
     | _ -> failwith "[Invalid argument] decision_twl: formula not in CNF";;

let rec unit_propagation_twl assignment f_map prop dl = 
    (*printf "PROPAGATION\n\n";*) match prop with 
        | [] -> (assignment, f_map, [])
        | x :: xs -> (
                      let Assignment (ys) = assignment in 
                       match x with
                        | Atom (y) -> let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Not (Atom (y))) in 
                                        (
                                         match conf with 
                                            | [] -> unit_propagation_twl (Assignment (ys @ [(y, true, false, dl)])) new_map (xs @ new_prop) dl
                                            | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_map, z :: zs)
                                        )
                        | Not (Atom (y)) -> let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Atom (y)) in 
                                        ( 
                                         match conf with
                                            | [] -> unit_propagation_twl (Assignment (ys @ [(y, false, false, dl)])) new_map (xs @ new_prop) dl
                                            | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_map, z :: zs)
                                        )
                        | _ -> failwith "[Invalid argument] unit_propagation_twl: list of propagation literals contains a non-literal element"
                     );;

let backjump_twl assignment formula conf = 
    (*printf "BACKJUMP\n\n";*) match assignment with 
        | Assignment (xs) -> (
                              match (find_backjump_clause xs formula conf) with
                                |(Disjunction (ys)) -> (
                                                        match (length ys) with 
                                                            | 0 -> let (zs, l) = (backjump_rec_twl assignment 0 (Disjunction (ys)) []) in 
                                                                    (Assignment (zs), l, Disjunction (ys))
                                                            | 1 -> let (zs, l) = (backjump_rec_twl assignment 0 (Disjunction (ys)) []) in
                                                                    (Assignment (zs), l, Disjunction (ys))
                                                            | _ ->  let (zs, l) = (backjump_rec_twl assignment (get_decision_level xs (hd (tl (rev ys)))) (Disjunction (ys)) []) in
                                                                    (Assignment (zs), l, Disjunction (ys))
                                                        )
                                | _ -> failwith "[Invalid argument] backjump_twl: find_backjump_clause did not return a clause"
                             );;

(* The target dl for backjump is always the hightest dl of any of the literals in the 
   backjump clause with exception for the single literal with current dl. So it's the 
   second highest dl in the clause overall. *)
let rec get_target_decision_level_rec rev_assignment clause count =
    match rev_assignment with 
        | (c, v, d, dl) :: xs -> let Disjunction (cs) = clause in
                                 if (mem (Atom (c)) cs) 
                                 then (
                                       if count < 1 
                                       then dl 
                                       else get_target_decision_level_rec xs clause (count - 1)
                                      )
                                 else (
                                       if (mem (Not (Atom (c))) cs)
                                       then (
                                             if count < 1 
                                             then dl
                                             else get_target_decision_level_rec xs clause (count - 1)
                                            )
                                       else get_target_decision_level_rec xs clause count
                                      )
        | _ -> failwith "[Invalid argument] get_target_decision_level_rec: assignment empty";;

let get_target_decision_level assignment clause = let Assignment (xs) = assignment in 
                                                  get_target_decision_level_rec (rev xs) clause 1;;

let rec get_last_assigned_literal rev_assignment clause =  
    match rev_assignment with 
        | (c, v, d, dl) :: xs -> let Disjunction (cs) = clause in
                                 if (mem (Atom (c)) cs) 
                                 then (Atom (c)) 
                                 else (
                                       if (mem (Not (Atom (c))) cs)
                                       then (Not (Atom (c)))
                                       else get_last_assigned_literal xs clause 
                                      )
        | _ -> failwith "[Invalid argument] get_last_assigned_literal: assignment empty";;

let rec backjump_rec_i assignment assignment_mutable dl clause ls = 
    match assignment_mutable with
        | Assignment ([]) -> failwith "[Invalid argument] backjump_rec: empty assignment"
        | Assignment ((c, v, d, l) :: xs) -> (
                                              match (compare l dl) with
                                                | 1 -> ( 
                                                        match clause with
                                                            | Disjunction ([]) -> (
                                                                                   match v with 
                                                                                    | true -> (ls @ [(c, false, false, dl)], Atom (c))
                                                                                    | false -> (ls @ [(c, true, false, dl)], Not (Atom (c)))
                                                                                  )
                                                            | Disjunction (ys) -> (
                                                                                   let Assignment (zs) = assignment in 
                                                                                   match (get_last_assigned_literal (rev zs) clause) with
                                                                                    | Atom (y) -> (ls @ [(y, true, false, dl)], Not (Atom (y)))
                                                                                    | Not (Atom (y)) -> (ls @ [(y, false, false, dl)], Atom (y))
                                                                                    | _ -> failwith "[Invalid argument] backjump_rec: last element of disjunction not a literal"
                                                                                  )
                                                            | _ -> failwith "[Invalid argument] backjump_rec: clause not a disjunction"
                                                       )
                                                | 0 -> backjump_rec_i assignment (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | -1 -> backjump_rec_i assignment (Assignment (xs)) dl clause (ls @ [(c, v, d, l)])
                                                | _ -> failwith "[Invalid argument] backjump_rec"
                                             );;

let rec num_last_dl_literals_rec rev_assignment clause dl result = 
    let Disjunction (xs) = clause in 
    match rev_assignment with 
        | (c, v, d, cdl) :: ys -> if dl = cdl 
                                  then (
                                        if ((mem (Atom (c)) xs) || (mem (Not (Atom (c))) xs))
                                        then num_last_dl_literals_rec ys clause dl (result + 1)
                                        else num_last_dl_literals_rec ys clause dl result
                                       )
                                  else result
        | _ -> failwith "[Invalid argument] num_last_dl_literals_rec: assignment empty";;

let num_last_dl_literals assignment clause dl = let Assignment (xs) = assignment in 
                                                num_last_dl_literals_rec (rev xs) clause dl 0;;

let rec resolve_rec c1 c2 l result = 
    match (c1, c2) with 
        | (Disjunction ([]), Disjunction ([])) -> result
        | (Disjunction (x :: xs), Disjunction ([])) -> (
                                                    match (x, l) with 
                                                     | (Atom (xa), Atom (a)) -> if xa = a 
                                                                                then resolve_rec (Disjunction (xs)) c2 l result
                                                                                else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                     | (Atom (xa), Not (Atom (a))) -> if xa = a 
                                                                                      then resolve_rec (Disjunction (xs)) c2 l result
                                                                                      else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                     | (Not (Atom (xa)), Atom (a)) -> if xa = a 
                                                                                      then resolve_rec (Disjunction (xs)) c2 l result
                                                                                      else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                     | (Not (Atom (xa)), Not (Atom (a))) -> if xa = a 
                                                                                            then resolve_rec (Disjunction (xs)) c2 l result
                                                                                            else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                       )
        | (Disjunction ([]), Disjunction (y :: ys)) -> (
                                                    match (y, l) with 
                                                     | (Atom (ya), Atom (a)) -> if ya = a 
                                                                                then resolve_rec c1 (Disjunction (ys)) l result
                                                                                else resolve_rec c1 (Disjunction (ys)) l (result @ [y])
                                                     | (Atom (ya), Not (Atom (a))) -> if ya = a 
                                                                                      then resolve_rec c1 (Disjunction (ys)) l result
                                                                                      else resolve_rec c1 (Disjunction (ys)) l (result @ [y])
                                                     | (Not (Atom (ya)), Atom (a)) -> if ya = a 
                                                                                      then resolve_rec c1 (Disjunction (ys)) l result
                                                                                      else resolve_rec c1 (Disjunction (ys)) l (result @ [y])
                                                     | (Not (Atom (ya)), Not (Atom (a))) -> if ya = a 
                                                                                            then resolve_rec c1 (Disjunction (ys)) l result
                                                                                            else resolve_rec c1 (Disjunction (ys)) l (result @ [y])
                                                       )
        | (Disjunction (x :: xs), Disjunction (y :: ys)) -> (
                                                    match (x, l) with 
                                                     | (Atom (xa), Atom (a)) -> if xa = a 
                                                                                then resolve_rec (Disjunction (xs)) c2 l result
                                                                                else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                     | (Atom (xa), Not (Atom (a))) -> if xa = a 
                                                                                      then resolve_rec (Disjunction (xs)) c2 l result
                                                                                      else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                     | (Not (Atom (xa)), Atom (a)) -> if xa = a 
                                                                                      then resolve_rec (Disjunction (xs)) c2 l result
                                                                                      else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                     | (Not (Atom (xa)), Not (Atom (a))) -> if xa = a 
                                                                                            then resolve_rec (Disjunction (xs)) c2 l result
                                                                                            else resolve_rec (Disjunction (xs)) c2 l (result @ [x])
                                                            )
        | _ -> failwith "[Invalid argument] resolve_rec: arguments are not clauses"
        ;;

let resolve c1 c2 l = Disjunction (Util.remove_duplicates (resolve_rec c1 c2 l []));; 

let rec find_backjump_clause_res_rec assignment clause up_map dl = 
    (* TODO: maybe check if chosen literal is of current dl, just to make sure *)
    let Assignment (xs) = assignment in 
    if (num_last_dl_literals assignment clause dl) < 2 
    then clause 
    else (
          match (get_last_assigned_literal (rev xs) clause) with 
            | Atom (x) -> ( 
                           match (UP_Map.find (Printing.print_element (Not (Atom (x)))) up_map) with 
                            | Disjunction ([]) -> failwith "[Invalid argument] find_backjump_clause_res_rec: Two non-propagated literals of the same level contained in a clause"
                            | Disjunction (y :: ys) -> find_backjump_clause_res_rec assignment (resolve clause (Disjunction (y :: ys)) (Atom (x))) up_map dl
                          )
            | Not (Atom (x)) -> ( 
                                 match (UP_Map.find (Printing.print_element (Atom (x))) up_map) with 
                                    | Disjunction ([]) -> failwith "[Invalid argument] find_backjump_clause_res_rec: Two non-propagated literals of the same level contained in a clause"
                                    | Disjunction (y :: ys) -> find_backjump_clause_res_rec assignment (resolve clause (Disjunction (y :: ys)) (Not (Atom (x)))) up_map dl
                                )
         );;

let find_backjump_clause_res assignment conf up_map dl = 
    let Assignment (xs) = assignment in
    match (get_last_assigned_literal (rev xs) conf) with 
        | Atom (x) -> (
                       match (UP_Map.find (Printing.print_element (Not (Atom (x)))) up_map) with 
                        | Disjunction ([]) -> if (num_last_dl_literals assignment conf dl) > 1 
                                              then failwith "[Invalid argument] find_backjump_clause_res"
                                              else conf
                        | Disjunction (y :: ys) -> find_backjump_clause_res_rec assignment (resolve conf (Disjunction (y :: ys)) (Atom (x))) up_map dl
                      )
        | Not (Atom (x)) -> (
                       match (UP_Map.find (Printing.print_element (Atom (x))) up_map) with 
                        | Disjunction ([]) -> if (num_last_dl_literals assignment conf dl) > 1 
                                              then failwith "[Invalid argument] find_backjump_clause_res"
                                              else conf
                        | Disjunction (y :: ys) -> find_backjump_clause_res_rec assignment (resolve conf (Disjunction (y :: ys)) (Not (Atom (x)))) up_map dl
                      );;

let backjump_twl_i assignment conf up_map dl = 
    (*printf "BACKJUMP\n";*)
    (*Printing.print_assignment assignment; printf "\n\n";
    printf "conf: %s\n" (Printing.print_element conf);*)
    match assignment with 
        | Assignment (xs) -> (
                              match (find_backjump_clause_res assignment conf up_map dl) with
                                |(Disjunction (ys)) -> (*printf "clause: %s\n\n" (Printing.print_element (Disjunction (ys)));*) (
                                                        match (length ys) with 
                                                            | 0 -> failwith "[Invalid argument] backjump_twl_i: conflict empty"
                                                                   (*let (zs, l) = (backjump_rec_twl assignment 0 (Disjunction (ys)) []) in 
                                                                    (Assignment (zs), l, Disjunction (ys))*)
                                                            | 1 -> (
                                                                    let (zs, l) = (backjump_rec_twl assignment 0 (Disjunction (ys)) []) in
                                                                                (Assignment (zs), l, Disjunction (ys), (UP_Map.add (Printing.print_element (hd ys)) (Disjunction ([])) up_map))
                                                                   )
                                                            | _ ->  let (zs, l) = (backjump_rec_i assignment assignment (get_target_decision_level assignment (Disjunction (ys))) (Disjunction (ys)) []) in
                                                                    (
                                                                     match l with  
                                                                        | Atom (x) -> (Assignment (zs), l, Disjunction (ys), (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction (ys)) up_map))
                                                                        | Not (Atom (x)) -> (Assignment (zs), l, Disjunction (ys), (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction (ys)) up_map))
                                                                    )
                                                        )
                                | _ -> failwith "[Invalid argument] backjump_twl: find_backjump_clause did not return a clause"
                             );;



(* How to use the map data structure: https://ocaml.org/learn/tutorials/map.html *)

let rec construct_watch_lists formula m = 
    match formula with
        | Formula (Conjunction ([])) -> m
        | Formula (Conjunction (x :: xs)) -> (
                                              match x with
                                                | Disjunction (w1 :: w2 :: ws) -> construct_watch_lists (Formula (Conjunction (xs))) (TWL_Map.add (Printing.print_element w2) ((TWL_Map.find (Printing.print_element w2) m) @ [x]) (TWL_Map.add (Printing.print_element w1) ((TWL_Map.find (Printing.print_element w1) m) @ [x]) m))
                                                | _ -> failwith "[Invalid argument] construct_watch_lists: clause contains less than 2 literals"
                                             )
        | _ -> failwith "[Invalid argument] construct_watch_lists: formula not in CNF";;

let rec add_clause_keys clause m literals = 
    match clause with
        | Disjunction ([]) -> (m, literals)
        | Disjunction (x :: xs) -> (
                                    match x with
                                        | Atom (y) -> add_clause_keys (Disjunction (xs)) (TWL_Map.add (Printing.print_element x) [] (TWL_Map.add (Printing.print_element (Not (Atom (y)))) [] m)) (literals @ [x])
                                        | Not (Atom (y)) -> add_clause_keys (Disjunction (xs)) (TWL_Map.add (Printing.print_element x) [] (TWL_Map.add (Printing.print_element (Atom (y))) [] m)) (literals @ [x])
                                        | _ -> failwith "[Invalid argument] add_clause_keys: clause contains non-literals"
                                   )
        | _ -> failwith "[Invalid argument] add_clause_keys: formula not in CNF or contains unit clauses";;

(* Before calling add_all_keys all unit clauses have to be removed from the formula *)
let rec add_all_keys formula_it formula m literals =
    match formula_it with
        | Formula (Conjunction ([])) -> (construct_watch_lists formula m, literals)
        | Formula (Conjunction (x :: xs)) -> (
                                              match x with 
                                                | Disjunction (y) -> let (new_m, lits) = (add_clause_keys x m literals) in add_all_keys (Formula (Conjunction (xs))) formula new_m lits
                                                | _ -> failwith "[Invalid argument] add_all_keys: formula must not contain unit clauses"
                                             )
        | _ -> failwith "[Invalid argument] add_all_keys: formula not in CNF";;

(* Needed for learning *)
let add_clause_to_map f_map clause = 
    match clause with 
        | Disjunction (w1 :: w2 :: ws) -> TWL_Map.add (Printing.print_element w2) ((TWL_Map.find (Printing.print_element w2) f_map) @ [clause]) (TWL_Map.add (Printing.print_element w1) ((TWL_Map.find (Printing.print_element w1) f_map) @ [clause]) f_map)
        | Disjunction ([w]) -> f_map
        | _ -> failwith "[Invalid argument] add_clause_to_map: argument not a clause";;

let construct_map formula = add_all_keys formula formula TWL_Map.empty [];;

(* removes unit clauses from the formula *)
let rec preprocess_unit_clauses_rec formula new_formula new_assignment prop to_update = 
    match formula with 
        | Formula (Conjunction ([])) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), prop, to_update)
        | Formula (Conjunction (x :: xs)) -> (
                                              match x with 
                                                | Disjunction (ys) -> preprocess_unit_clauses_rec (Formula (Conjunction (xs))) (new_formula @ [x]) new_assignment prop to_update
                                                | Atom (y) -> if (is_assigned (Assignment (new_assignment)) x)
                                                              then preprocess_unit_clauses_rec (Formula (Conjunction (xs))) new_formula new_assignment prop to_update
                                                              else preprocess_unit_clauses_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (prop @ [x]) (to_update @ [x])
                                                | Not (Atom (y)) -> if (is_assigned (Assignment (new_assignment)) x)
                                                                    then preprocess_unit_clauses_rec (Formula (Conjunction (xs))) new_formula new_assignment prop to_update
                                                                    else preprocess_unit_clauses_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (prop @ [x]) (to_update @ [x])
                                                | _ -> failwith "[Invalid argument] preprocess_unit_clauses_rec: formula not in CNF"
                                             )
        | _ -> failwith "[Invalid argument] preprocess_unit_clauses_rec: formula not in CNF";;

let preprocess_unit_clauses (Assignment (assignment)) formula = preprocess_unit_clauses_rec formula [] assignment [] [];;

let rec preserve_unit_assignments_rec (Assignment (assignment)) result = 
    match assignment with
        | (c, v, false, 0) :: xs -> preserve_unit_assignments_rec (Assignment (xs)) (result @ [(c, v, false, 0)])
        | _ -> result;;

let preserve_unit_assignments assignment = Assignment (preserve_unit_assignments_rec assignment []);;

let rec dpll_twl_rec assignment formula f_map literals dl = 
    (*Printing.print_assignment assignment; printf "\n\n";*) match model_found_twl assignment formula with
        | true -> (
                   match (Util.to_simplex_format_init assignment) with 
                    | (sf_assignment, cs) -> ( 
                                              (*Printing.print_assignment assignment; printf "\n\n";*) (*Printing.print_simplex_constraints sf_assignment;*) 
                                              match Simplex.simplex sf_assignment with
                                                | Some (x) -> (*
                                                               match x with
                                                                | Mapping (RBT (Empty)) -> (*printf "Maybe\n";*) true
                                                                | Mapping (RBT (_)) -> true
                                                              *)
                                                              (*Printing.print_assignment assignment; printf "\n\n";*)
                                                              true
                                                | None -> (
                                                           match cs with 
                                                            | Assignment ([z]) -> (
                                                                                   match z with
                                                                                    | (y, true, d, l) -> restart_twl_unit assignment formula f_map literals y false
                                                                                    | (y, false, d, l) -> restart_twl_unit assignment formula f_map literals y true
                                                                                  )
                                                            | Assignment (zs) -> let ys = (Disjunction (transform_to_neg_clause cs)) in 
                                                                                    (*printf "restart\n\n";*) restart_twl assignment (learn formula ys) (add_clause_to_map f_map ys) literals
                                                          )
                                             )
                  )
        | false -> let (new_assignment, new_map, new_dl, prop, conf) = decision_twl formula assignment f_map dl in 
                    (
                     match conf with 
                        | [] -> (
                                 match prop with
                                    | [] -> dpll_twl_rec new_assignment formula new_map literals new_dl
                                    | x :: xs -> let (n_assignment, n_map, n_conf) = unit_propagation_twl new_assignment new_map prop new_dl in 
                                                    (
                                                     match n_conf with
                                                      | [] -> (
                                                               match (Util.to_simplex_format_init n_assignment) with 
                                                                    | (sf_assignment, cs) -> ( 
                                                                                            (*Printing.print_assignment n_assignment; printf "\n\n"; Printing.print_simplex_constraints sf_assignment; printf "\n\n";*)
                                                                                             match Simplex.simplex sf_assignment with
                                                                                                | Some (x) -> dpll_twl_rec n_assignment formula n_map literals new_dl
                                                                                                | None -> (
                                                                                                            match cs with 
                                                                                                                | Assignment ([z]) -> (
                                                                                                                                       match z with
                                                                                                                                        | (y, true, d, l) -> restart_twl_unit n_assignment formula f_map literals y false
                                                                                                                                        | (y, false, d, l) -> restart_twl_unit n_assignment formula f_map literals y true
                                                                                                                                      )
                                                                                                                | Assignment (zs) -> let ys = (Disjunction (transform_to_neg_clause cs)) in 
                                                                                                                                        (*printf "restart\n\n";*) restart_twl n_assignment (learn formula ys) (add_clause_to_map f_map ys) literals
                                                                                                          )
                                                                                            )
                                                              )
                                                      | x :: xs -> (
                                                                    let (ys, _, bj_clause) = (backjump_twl n_assignment formula (hd n_conf)) in 
                                                                        (
                                                                         (*printf "backjump\n\n";*) match (bj_clause, (conflict_exists ys formula)) with
                                                                            | (_, true) -> false
                                                                            | (Disjunction ([]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                                                            | (Disjunction ([z]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                                                            | (Disjunction (zs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_rec ys formula_l (add_clause_to_map new_map bj_clause) literals (get_current_decision_level ys)
                                                                            | _ -> failwith "[Invalid argument] dpll_twl_rec: backjump clause is not a clause"
                                                                        )
                                                                   )
                                                    )
                                )
                        | x :: xs -> (
                                      let (ys, _, bj_clause) = (backjump_twl new_assignment formula (hd conf)) in 
                                        (
                                         (*printf "backjump\n\n";*) match (bj_clause, (conflict_exists ys formula)) with
                                            | (_, true) -> false
                                            | (Disjunction ([]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                            | (Disjunction ([z]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                            | (Disjunction (zs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_rec ys formula_l (add_clause_to_map new_map bj_clause) literals (get_current_decision_level ys)
                                            | _ -> failwith "[Invalid argument] dpll_twl_rec: backjump clause is not a clause"
                                        )
                                     )
                                      
                    )

and dpll_twl formula = let (new_formula, new_assignment, prop, to_update) = preprocess_unit_clauses (Assignment ([])) formula in 
                        (*Printing.print_formula new_formula; printf "\n\n";*) let (f_map, literals) = construct_map new_formula in 
                            let (n_assignment, n_map, conf) = unit_propagation_twl new_assignment f_map prop 0 in 
                                (
                                 match conf with
                                    | [] -> dpll_twl_rec n_assignment new_formula n_map literals 0
                                    | x :: xs -> false
                                )

and restart_twl assignment formula f_map literals = let (new_formula, new_assignment, prop, to_update) = preprocess_unit_clauses (preserve_unit_assignments assignment) formula in 
                                            let (f_map_new, prop_new, conf_new) = update_watch_lists_l new_assignment f_map to_update in
                                             let (n_assignment, n_map, conf) = unit_propagation_twl new_assignment f_map_new prop 0 in 
                                                (
                                                 match conf with
                                                    | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) dpll_twl_rec n_assignment new_formula n_map literals 0
                                                    | x :: xs -> false
                                                )
                                                
and restart_twl_unit assignment formula f_map literals unit_literal lit_val = let (new_formula, new_assignment, prop, to_update) = preprocess_unit_clauses (preserve_unit_assignments assignment) formula in
                                                            let (f_map_new, prop_new, conf_new) = update_watch_lists_l new_assignment f_map to_update in
                                                            let Assignment (xs) = new_assignment in
                                                             if (is_assigned new_assignment (Atom (unit_literal)))
                                                             then false
                                                             else (
                                                                let (n_assignment, n_map, conf) = unit_propagation_twl (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) f_map_new prop 0 in 
                                                                    (
                                                                    match conf with
                                                                        | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) dpll_twl_rec n_assignment new_formula n_map literals 0
                                                                        | x :: xs -> false
                                                                    )
                                                                  );;

(**********************************************)

(****************************************************************************************************)
(* Two-watched-literal implementation using incremental simplex, unsat cores and theory propagation *)
(****************************************************************************************************)

let rec convert_unsat_core_rec unsat_core inv_map result =
    match unsat_core with
        | [] -> result
        | x :: xs -> (
                      match (Tseitin.Inv_Map.find (int_of_big_int (Simplex_inc.integer_of_nat x)) inv_map) with
                        | (y, true, _, _) -> convert_unsat_core_rec xs inv_map (result @ [(Atom (y))])
                        | (y, false, _, _) -> convert_unsat_core_rec xs inv_map (result @ [(Not (Atom (y)))])
                     );;

let convert_unsat_core unsat_core inv_map = convert_unsat_core_rec unsat_core inv_map [];;

let rec convert_unsat_core_i_rec unsat_core i_map inv_map result =
    match unsat_core with
        | [] -> result
        | x :: xs -> (
                      let i = (int_of_big_int (Simplex_inc.integer_of_nat x)) in
                       match (Tseitin.Inv_Map.find i inv_map) with
                        | (y, true, _, _) -> convert_unsat_core_i_rec xs i_map inv_map (result @ [(Atom (Index (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map)))])
                        | (y, false, _, _) -> convert_unsat_core_i_rec xs i_map inv_map (result @ [(Not (Atom (Index (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))))])
                     );;

let convert_unsat_core_i unsat_core i_map inv_map = convert_unsat_core_i_rec unsat_core i_map inv_map [];;

let rec get_checkpoint checkpoints dl = 
    match checkpoints with
        | [] -> failwith "[Invalid argument] no simplex checkpoint for target decision level"
        | (l, cp) :: xs -> (
                            match compare l dl with
                                | 0 -> cp
                                | _ -> get_checkpoint xs dl
                           );;

let rec reset_checkpoints_rec cps dl result = 
    match cps with
        | [] -> failwith "[Invalid argument] reset_checkpoints: no checkpoint for target decision level"
        | (l, cp) :: xs -> (
                            match compare l dl with
                                | -1 -> reset_checkpoints_rec xs dl (result @ [(l, cp)])
                                | _ -> result
                           );;

let reset_checkpoints cps dl = reset_checkpoints_rec cps dl [];;

let rec backjump_to_conflictless_state_rec formula assignment assignment_mutable up_map checkpoints bj_dl i_map inv_map state result =
    (*printf "bj_dl %s\n" (string_of_int bj_dl);*) match (assignment_mutable, bj_dl) with
        | (Assignment ([]), _) -> failwith "[Invalid argument] backjump_to_conflictless_state_rec: target decision level too high"
        | (Assignment (_), 0) -> ([], up_map, checkpoints, state, 0, Atom (AuxVar (-1)))
        | (Assignment ((c, v, d, dl) :: xs), _) -> if dl = bj_dl
                                                   then ( 
                                                         match v with 
                                                          | true -> (*Printing.print_assignment (Assignment (result @ [(c, false, false, dl - 1)])); printf "\n";*) if (conflict_exists_i (Assignment (result @ [(c, false, false, dl - 1)])) formula) 
                                                                    then (backjump_to_conflictless_state_rec formula assignment assignment up_map checkpoints (bj_dl - 1) i_map inv_map state [])
                                                                    else (
                                                                          if (is_proper_constraint c)
                                                                          then ( 
                                                                                match c with
                                                                                | (Index (x)) -> let (xc, xv, xd, xdl) = (Tseitin.Inv_Map.find x inv_map) in
                                                                                                (
                                                                                                match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n xc)) i_map))) (Simplex_inc.backtrack_simplex (get_checkpoint checkpoints (dl - 1)) state) with
                                                                                                    | Inl (unsat_core) -> backjump_to_conflictless_state_rec (learn formula (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map))) assignment assignment up_map checkpoints (bj_dl - 1) i_map inv_map state []
                                                                                                    | Inr (n_state) -> (result @ [(c, false, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), n_state, (dl - 1), Atom (c))
                                                                                                )
                                                                                | (Constraint (x)) -> failwith "Non-index version of function backjump_to_conflictless_state_rec not implemented yet"
                                                                               )
                                                                          else (result @ [(c, false, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), (Simplex_inc.backtrack_simplex (get_checkpoint checkpoints (dl - 1)) state), (dl - 1), Atom (c))
                                                                         )
                                                          | false -> (*Printing.print_assignment (Assignment (result @ [(c, true, false, dl - 1)])); printf "\n";*) if (conflict_exists_i (Assignment (result @ [(c, true, false, dl - 1)])) formula) 
                                                                     then (backjump_to_conflictless_state_rec formula assignment assignment up_map checkpoints (bj_dl - 1) i_map inv_map state [])
                                                                     else ( 
                                                                           if (is_proper_constraint c)
                                                                           then (
                                                                                 match c with
                                                                                | (Index (x)) -> (
                                                                                                  match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int x)) (Simplex_inc.backtrack_simplex (get_checkpoint checkpoints (dl - 1)) state) with
                                                                                                    | Inl (unsat_core) -> backjump_to_conflictless_state_rec (learn formula (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map))) assignment assignment up_map checkpoints (bj_dl - 1) i_map inv_map state []
                                                                                                    | Inr (n_state) -> (result @ [(c, true, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), n_state, (dl - 1), Not (Atom (c)))
                                                                                                 )
                                                                                | (Constraint (x)) -> failwith "Non-index version of function backjump_to_conflictless_state_rec not implemented yet"
                                                                                )
                                                                           else (result @ [(c, true, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), (Simplex_inc.backtrack_simplex (get_checkpoint checkpoints (dl - 1)) state), (dl - 1), Not (Atom (c)))
                                                                          )
                                                        )
                                                   else backjump_to_conflictless_state_rec formula assignment (Assignment (xs)) up_map checkpoints bj_dl i_map inv_map state (result @ [(c, v, d, dl)]);;

let backjump_to_conflictless_state formula assignment up_map checkpoints dl i_map inv_map state = (*printf "BJ_CONFLESS\n\n";*) backjump_to_conflictless_state_rec formula assignment assignment up_map checkpoints dl i_map inv_map state [];;

let rec minimal_assignment_for_unsat_core_rec assignment unsat_core result = 
    (*printf "minimal_assignment\n\n";*) match assignment with
        | Assignment ([]) -> failwith "[Invalid argument] minimal_assignment_for_unsat_core_rec"
        | Assignment (x :: xs) -> (
                                   match (unassigned_or_true_i (Assignment (result @ [x])) unsat_core) with
                                    | [] -> (result @ [x])
                                    | ys -> minimal_assignment_for_unsat_core_rec (Assignment (xs)) unsat_core (result @ [x])
                                  );;

let minimal_assignment_for_unsat_core assignment unsat_core = (*printf "BACKJUMP\n\n";*) minimal_assignment_for_unsat_core_rec assignment unsat_core [];;

let rec t_backjump formula assignment limit = 
    (*printf "T_BJ\n\n";*) match assignment with
        | [] -> (assignment, Atom (AuxVar (-1)), false)
        | (c, v, d, dl) :: xs -> (
                                  (*match d with
                                    | false -> t_backjump formula xs
                                    | true -> (
                                               match v with
                                                | true -> if (conflict_exists_i (Assignment (rev ((c, false, false, dl - 1) :: xs))) formula)
                                                          then (
                                                                if dl < 1
                                                                then (rev assignment, Atom (c), false)
                                                                else t_backjump formula xs
                                                                )
                                                          else (rev ((c, false, false, dl - 1) :: xs), Atom (c), true)
                                                | false -> if (conflict_exists_i (Assignment (rev ((c, true, false, dl - 1) :: xs))) formula)
                                                          then (
                                                                if dl < 1
                                                                then (rev assignment, Not (Atom (c)), false)
                                                                else t_backjump formula xs
                                                                )
                                                          else (rev ((c, true, false, dl - 1) :: xs), Not (Atom (c)), true)
                                              )*)

                                    match d with
                                        | false -> t_backjump formula xs limit
                                        | true -> (
                                                   match v with
                                                    | true -> if (conflict_exists_i (Assignment (rev ((c, false, false, dl - 1) :: xs))) formula)
                                                              then (
                                                                    if limit > 0
                                                                    then t_backjump formula xs (limit - 1)
                                                                    else (rev ((c, false, false, dl - 1) :: xs), Atom (c), false)
                                                                   )
                                                              else (rev ((c, false, false, dl - 1) :: xs), Atom (c), true)
                                                    | false -> if (conflict_exists_i (Assignment (rev ((c, true, false, dl - 1) :: xs))) formula)
                                                               then (
                                                                     if limit > 0
                                                                     then t_backjump formula xs (limit - 1)
                                                                     else (rev ((c, true, false, dl - 1) :: xs), Not (Atom (c)), false)
                                                                    )
                                                               else (rev ((c, true, false, dl - 1) :: xs), Not (Atom (c)), true)
                                                  )
                                 );;

let rec preprocess_unit_clauses_inc_rec formula new_formula new_assignment prop conf s_state i_map inv_map to_update =
    match formula with 
        | Formula (Conjunction ([])) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), prop, conf, s_state, to_update)
        | Formula (Conjunction (x :: xs)) -> (
                                              match x with 
                                                | Disjunction (ys) -> preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) (new_formula @ [x]) new_assignment prop conf s_state i_map inv_map to_update
                                                | Atom (y) -> if is_proper_constraint y 
                                                              then (
                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))) s_state with
                                                                        | Inl (unsat_core) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), prop, true, s_state, to_update)
                                                                        | Inr (n_state) -> if (is_assigned (Assignment (new_assignment)) (Atom (y)))
                                                                                           then preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula new_assignment prop conf n_state i_map inv_map to_update
                                                                                           else preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (prop @ [x]) conf n_state i_map inv_map (to_update @ [(Not (Atom (y)))])
                                                                   )
                                                              else (
                                                                    if (is_assigned (Assignment (new_assignment)) (Atom (y)))
                                                                    then preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula new_assignment prop conf s_state i_map inv_map to_update
                                                                    else preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (prop @ [x]) conf s_state i_map inv_map to_update
                                                                   )
                                                | Not (Atom (y)) -> if is_proper_constraint y 
                                                                    then (
                                                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n y) i_map))) s_state with
                                                                                | Inl (unsat_core) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), prop, true, s_state, to_update)
                                                                                | Inr (n_state) -> if (is_assigned (Assignment (new_assignment)) (Atom (y)))
                                                                                                   then preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula new_assignment prop conf n_state i_map inv_map to_update
                                                                                                   else preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (prop @ [x]) conf n_state i_map inv_map (to_update @ [(Atom (y))])
                                                                        )
                                                                    else (
                                                                          if (is_assigned (Assignment (new_assignment)) (Atom (y)))  
                                                                          then preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula new_assignment prop conf s_state i_map inv_map to_update
                                                                          else preprocess_unit_clauses_inc_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (prop @ [x]) conf s_state i_map inv_map to_update
                                                                         )
                                                | _ -> failwith "[Invalid argument] preprocess_unit_clauses_inc_rec: formula not in CNF"
                                             )
        | _ -> failwith "[Invalid argument] preprocess_unit_clauses_inc_rec: formula not in CNF";;

let preprocess_unit_clauses_inc (Assignment (assignment)) formula s_state i_map inv_map = preprocess_unit_clauses_inc_rec formula [] assignment [] false s_state i_map inv_map [];;

let rec preprocess_unit_clauses_inc_i_rec formula new_formula new_assignment up_map prop conf s_state i_map inv_map to_update =
    match formula with 
        | Formula (Conjunction ([])) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), up_map, prop, conf, s_state, to_update)
        | Formula (Conjunction (x :: xs)) -> (
                                              match x with 
                                                | Disjunction (ys) -> preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) (new_formula @ [x]) new_assignment up_map prop conf s_state i_map inv_map to_update
                                                | Atom (y) -> if is_proper_constraint y 
                                                              then (
                                                                    match y with 
                                                                    | Constraint (z) -> (
                                                                                         match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))) s_state with
                                                                                            | Inl (unsat_core) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), up_map, prop, true, s_state, to_update)
                                                                                            | Inr (n_state) -> if (is_assigned_i (Assignment (new_assignment)) (Atom (y)))
                                                                                                               then preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula new_assignment up_map prop conf n_state i_map inv_map to_update
                                                                                                               else preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (UP_Map.add (Printing.print_element x) (Disjunction ([])) up_map) (prop @ [(x, Disjunction ([]))]) conf n_state i_map inv_map (to_update @ [(Not (Atom (y)))])
                                                                                        )
                                                                    | Index (z) -> (
                                                                                         match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int z)) s_state with
                                                                                            | Inl (unsat_core) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), up_map, prop, true, s_state, to_update)
                                                                                            | Inr (n_state) -> if (is_assigned_i (Assignment (new_assignment)) (Atom (y)))
                                                                                                               then preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula new_assignment up_map prop conf n_state i_map inv_map to_update
                                                                                                               else (preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (UP_Map.add (Printing.print_element x) (Disjunction ([])) up_map) (prop @ [(x, Disjunction ([]))]) conf n_state i_map inv_map (to_update @ [(Not (Atom (y)))]))
                                                                                   )
                                                                   )
                                                              else (
                                                                    if (is_assigned_i (Assignment (new_assignment)) (Atom (y)))
                                                                    then preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula new_assignment up_map prop conf s_state i_map inv_map to_update
                                                                    else ( preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (UP_Map.add (Printing.print_element x) (Disjunction ([])) up_map) (prop @ [(x, Disjunction ([]))]) conf s_state i_map inv_map (to_update @ [(Not (Atom (y)))]))
                                                                   )
                                                | Not (Atom (y)) -> if is_proper_constraint y 
                                                                    then (
                                                                          match y with
                                                                           | Constraint (z) -> (
                                                                                                match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n y) i_map))) s_state with
                                                                                                    | Inl (unsat_core) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), up_map, prop, true, s_state, to_update)
                                                                                                    | Inr (n_state) -> if (is_assigned_i (Assignment (new_assignment)) (Atom (y)))
                                                                                                                       then preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula new_assignment up_map prop conf n_state i_map inv_map to_update
                                                                                                                       else preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (UP_Map.add (Printing.print_element x) (Disjunction ([])) up_map) (prop @ [(x, Disjunction ([]))]) conf n_state i_map inv_map (to_update @ [(Atom (y))])                  
                                                                                               )
                                                                           | Index (z) -> (
                                                                                           let (c, v, d, dl) = (Tseitin.Inv_Map.find z inv_map) in
                                                                                           match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) s_state with
                                                                                                | Inl (unsat_core) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), up_map, prop, true, s_state, to_update)
                                                                                                | Inr (n_state) -> if (is_assigned_i (Assignment (new_assignment)) (Atom (y)))
                                                                                                                   then preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula new_assignment up_map prop conf n_state i_map inv_map to_update
                                                                                                                   else (preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (UP_Map.add (Printing.print_element x) (Disjunction ([])) up_map) (prop @ [(x, Disjunction ([]))]) conf n_state i_map inv_map (to_update @ [(Atom (y))]))
                                                                                          )
                                                                        )
                                                                    else (
                                                                          if (is_assigned_i (Assignment (new_assignment)) (Atom (y)))  
                                                                          then preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula new_assignment up_map prop conf s_state i_map inv_map to_update
                                                                          else (preprocess_unit_clauses_inc_i_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (UP_Map.add (Printing.print_element x) (Disjunction ([])) up_map) (prop @ [(x, Disjunction ([]))]) conf s_state i_map inv_map (to_update @ [(Atom (y))]))
                                                                        )
                                                | _ -> failwith "[Invalid argument] preprocess_unit_clauses_inc_rec: formula not in CNF"
                                             )
        | _ -> failwith "[Invalid argument] preprocess_unit_clauses_inc_rec: formula not in CNF";;

let preprocess_unit_clauses_inc_i (Assignment (assignment)) formula up_map s_state i_map inv_map = preprocess_unit_clauses_inc_i_rec formula [] assignment up_map [] false s_state i_map inv_map [];;

let rec decision_twl_inc formula assignment f_map s_state i_map inv_map dl =
    match formula with
     | Formula (Conjunction (cs)) -> ( 
                                    match contains_unassigned_literal assignment (hd cs) with
                                        | false -> decision_twl_inc (Formula (Conjunction (tl cs))) assignment f_map s_state i_map inv_map dl
                                        | true -> (
                                                    let Assignment (xs) = assignment in
                                                    match choose_decision_literal assignment (hd cs) with
                                                        | Atom (x) -> if is_proper_constraint x
                                                                    then (
                                                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map))) s_state with
                                                                                | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), f_map, dl + 1, s_state, [], convert_unsat_core unsat_core inv_map)
                                                                                | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Not (Atom (x))) in 
                                                                                                    (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, n_state, prop, conf)
                                                                        )
                                                                    else (  
                                                                            let (new_map, prop, conf) = update_watch_lists assignment f_map (Not (Atom (x))) in 
                                                                                (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, s_state, prop, conf)
                                                                        )
                                                        | Not (Atom (x)) -> if is_proper_constraint x
                                                                            then (
                                                                                match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n x) i_map))) s_state with
                                                                                    | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), f_map, dl + 1, s_state, [], convert_unsat_core unsat_core inv_map)
                                                                                    | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Atom (x)) in 
                                                                                                            (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, n_state, prop, conf)
                                                                                )
                                                                            else (
                                                                                let (new_map, prop, conf) = update_watch_lists assignment f_map (Atom (x)) in
                                                                                    (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, s_state, prop, conf) 
                                                                                )
                                                        | _ -> failwith "[Invalid argument] decision_twl_inc: choose_decision_literal did not return a literal"
                                                )
                                     )
     | _ -> failwith "[Invalid argument] decision_twl_inc: formula not in CNF";;

(*let t_propagation_i assignment assigned_map f_map state i_map inv_map literal = 
    match literal with 
        | Atom (Index (x)) -> (
                               let (c, v, d, dl) = (Tseitin.Inv_Map.find x inv_map) in 
                                match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map))) state with
                                    | Inl (unsat_core) -> (f_map, state, [], [Disjunction (convert_unsat_core_i unsat_core i_map inv_map)])
                                    | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment assigned_map f_map literal in 
                                                       (new_map, n_state, prop, conf)
                              )
        | Not (Atom (Index (x))) -> (
                                    let (c, v, d, dl) = (Tseitin.Inv_Map.find x inv_map) in 
                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map))) state with
                                            | Inl (unsat_core) -> (f_map, state, [], [Disjunction (convert_unsat_core_i unsat_core i_map inv_map)])
                                            | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment assigned_map f_map literal in 
                                                               (new_map, n_state, prop, conf)
                                    )
        | _ -> failwith "[Invalid argument] t_propagation_i";;*)

let rec choose_decision_literal_vsids assignment vsids = 
    match vsids with 
     | [] -> []
     | (l, v) :: vs -> if is_assigned_i assignment l 
                       then choose_decision_literal_vsids assignment vs 
                       else [l];;

(*let rec decision_twl_inc_i_no_vsids formula assignment f_map up_map s_state i_map inv_map dl conf_count =
    (*printf "DECISION\n\n";*) match formula with
     | Formula (Conjunction ([])) -> (assignment, f_map, dl, up_map, s_state, [], [], true)
     | Formula (Conjunction (cs)) -> ( 
                                    (*match contains_unassigned_literal_i assignment (hd cs) with
                                        | false -> decision_twl_inc_i (Formula (Conjunction (tl cs))) assignment f_map s_state i_map inv_map dl
                                        | true -> ( *)
                                                    let Assignment (xs) = assignment in
                                                     match (choose_decision_literal_i assignment (hd cs)) with
                                                        | [] -> decision_twl_inc_i_no_vsids (Formula (Conjunction (tl cs))) assignment f_map up_map s_state i_map inv_map dl conf_count
                                                        | [Atom (x)] -> (*printf "decision literal: %s\n\n" (Printing.print_constraint_n x);*)
                                                                    if is_proper_constraint x
                                                                    then (
                                                                          match x with 
                                                                            | Constraint (y) -> (
                                                                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map))) s_state with
                                                                                                    | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                    | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (x))) in 
                                                                                                                            (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                                                )   
                                                                            | Index (y) -> (
                                                                                            let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in
                                                                                            (*printf ("decision, atom: %s\n") (Printing.print_constraint_n s);*)
                                                                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int y)) s_state with
                                                                                                | Inl (unsat_core) -> (*printf "unsat_core\n";*) 
                                                                                                                      (*if true
                                                                                                                      then*) (Assignment (xs @ [(x, true, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                                      (*else let (new_map, new_state, prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Atom (x)) in
                                                                                                                       (Assignment (xs @ [(x, false, false, dl)]), new_map, dl, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), new_state, prop, conf, false)*)
                                                                                                | Inr (n_state) -> (*printf "state\n";*) let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (x))) in 
                                                                                                                        (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                                           )   
                                                                        )
                                                                    else (  
                                                                            let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (x))) in 
                                                                                 (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, prop, conf, false)
                                                                        )
                                                        | [Not (Atom (x))] -> (*printf "decision literal: Not %s\n\n" (Printing.print_constraint_n x);*) 
                                                                            if is_proper_constraint x
                                                                            then (
                                                                                  match x with
                                                                                    | Constraint (y) -> (
                                                                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n x) i_map))) s_state with
                                                                                                            | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                            | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Atom (x)) in 
                                                                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                                                        )
                                                                                    | Index (y) -> (
                                                                                                    let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in 
                                                                                                    (*printf ("decision, not atom: %s\n") (Printing.print_constraint_n c);*)
                                                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map))) s_state with
                                                                                                        | Inl (unsat_core) -> (*printf "unsat_core\n";*) 
                                                                                                                             (*if true 
                                                                                                                             then*) (Assignment (xs @ [(x, false, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                                             (*else let (new_map, new_state, prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Not (Atom (x))) in
                                                                                                                                (Assignment (xs @ [(x, true, false, dl)]), new_map, dl, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), new_state, prop, conf, false)*)
                                                                                                        | Inr (n_state) -> (*printf "state\n";*) let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Atom (x)) in 
                                                                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                                                   )
                                                                                )
                                                                            else (
                                                                                let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Atom (x)) in
                                                                                  (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, prop, conf, false) 
                                                                                )
                                                        | _ -> failwith "[Invalid argument] decision_twl_inc: choose_decision_literal did not return a literal"
                                                )
                                     (*)*)
     | _ -> failwith "[Invalid argument] decision_twl_inc: formula not in CNF";;*)

(*let rec decision_twl_inc_i formula assignment f_map up_map vsids s_state i_map inv_map dl conf_count =
    (*printf "DECISION\n";*) match formula with
     | Formula (Conjunction ([])) -> (assignment, f_map, dl, up_map, s_state, [], [], true)
     | Formula (Conjunction (cs)) -> ( 
                                    (*match contains_unassigned_literal_i assignment (hd cs) with
                                        | false -> decision_twl_inc_i (Formula (Conjunction (tl cs))) assignment f_map s_state i_map inv_map dl
                                        | true -> ( *)
                                                    let Assignment (xs) = assignment in
                                                     (*match (choose_decision_literal_i assignment (hd cs)) with*)
                                                     match (choose_decision_literal_vsids assignment vsids) with 
                                                        | [] -> decision_twl_inc_i_no_vsids (Formula (Conjunction (tl cs))) assignment f_map up_map s_state i_map inv_map dl conf_count
                                                        | [Atom (x)] -> (*printf "decision literal: %s\n\n" (Printing.print_constraint_n x);*)
                                                                    if is_proper_constraint x
                                                                    then (
                                                                          match x with 
                                                                            | Constraint (y) -> (
                                                                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map))) s_state with
                                                                                                    | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                    | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (x))) in 
                                                                                                                            (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                                                )   
                                                                            | Index (y) -> (
                                                                                            let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in
                                                                                            (*printf ("decision, atom: %s\n") (Printing.print_constraint_n s);*)
                                                                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int y)) s_state with
                                                                                                | Inl (unsat_core) -> (*printf "unsat_core\n";*) 
                                                                                                                      (*if true
                                                                                                                      then*) (Assignment (xs @ [(x, true, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                                      (*else let (new_map, new_state, prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Atom (x)) in
                                                                                                                       (Assignment (xs @ [(x, false, false, dl)]), new_map, dl, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), new_state, prop, conf, false)*)
                                                                                                | Inr (n_state) -> (*printf "state\n";*) let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (x))) in 
                                                                                                                        (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                                           )   
                                                                        )
                                                                    else (  
                                                                            let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (x))) in
                                                                                (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, prop, conf, false)
                                                                        )
                                                        | [Not (Atom (x))] -> (*printf "decision literal: Not %s\n\n" (Printing.print_constraint_n x);*)
                                                                            if is_proper_constraint x
                                                                            then (
                                                                                  match x with
                                                                                    | Constraint (y) -> (
                                                                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n x) i_map))) s_state with
                                                                                                            | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                            | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Atom (x)) in 
                                                                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                                                        )
                                                                                    | Index (y) -> (
                                                                                                    let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in 
                                                                                                    (*printf ("decision, not atom: %s\n") (Printing.print_constraint_n c);*)
                                                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map))) s_state with
                                                                                                        | Inl (unsat_core) -> (*printf "unsat_core\n";*) 
                                                                                                                             (*if true
                                                                                                                             then*) (Assignment (xs @ [(x, false, true, dl + 1)]), f_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                                             (*else let (new_map, new_state, prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Not (Atom (x))) in
                                                                                                                                (Assignment (xs @ [(x, true, false, dl)]), new_map, dl, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), new_state, prop, conf, false)*)
                                                                                                        | Inr (n_state) -> (*printf "state\n";*) let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Atom (x)) in 
                                                                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                                                   )
                                                                                )
                                                                            else (
                                                                                let (new_map, prop, conf) = update_watch_lists_i assignment f_map (Atom (x)) in
                                                                                    (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, prop, conf, false) 
                                                                                )
                                                        | _ -> failwith "[Invalid argument] decision_twl_inc: choose_decision_literal did not return a literal"
                                                )
                                     (*)*)
     | _ -> failwith "[Invalid argument] decision_twl_inc: formula not in CNF";;*)

let rec choose_decision_literal_i_map assignment assigned_map clause = 
        (
         match clause with
            | Disjunction ([]) -> []
            | Disjunction (x :: xs) -> if is_assigned_i_map assignment assigned_map x 
                                       then choose_decision_literal_i_map assignment assigned_map (Disjunction (xs))
                                       else [x]
            | _ -> failwith "[Invalid argument] choose_decision_literal: argument not a clause"
        );;

let rec decision_twl_inc_i_map formula assignment assigned_map f_map up_map s_state i_map inv_map dl conf_count =
    (*printf "DECISION\n\n";*) match formula with
     | Formula (Conjunction ([])) -> (assignment, assigned_map, f_map, dl, up_map, s_state, [], [], true)
     | Formula (Conjunction (cs)) -> ( 
                                    (*match contains_unassigned_literal_i assignment (hd cs) with
                                        | false -> decision_twl_inc_i (Formula (Conjunction (tl cs))) assignment f_map s_state i_map inv_map dl
                                        | true -> ( *)
                                                    let Assignment (xs) = assignment in
                                                     match (choose_decision_literal_i_map assignment assigned_map (hd cs)) with
                                                        | [] -> decision_twl_inc_i_map (Formula (Conjunction (tl cs))) assignment assigned_map f_map up_map s_state i_map inv_map dl conf_count
                                                        | [Atom (x)] -> (*printf "decision literal: %s\n\n" (Printing.print_constraint_n x);*)
                                                                    if is_proper_constraint x
                                                                    then (
                                                                          match x with 
                                                                            | Constraint (y) -> (
                                                                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map))) s_state with
                                                                                                    | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), assigned_map, f_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                    | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment assigned_map f_map (Not (Atom (x))) in 
                                                                                                                            (Assignment (xs @ [(x, true, true, dl + 1)]), assigned_map, new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                                                )   
                                                                            | Index (y) -> (
                                                                                            let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in
                                                                                            (*printf ("decision, atom: %s\n") (Printing.print_constraint_n s);*)
                                                                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int y)) s_state with
                                                                                                | Inl (unsat_core) -> (*printf "unsat_core\n";*) 
                                                                                                                      (*if true
                                                                                                                      then*) 
                                                                                                                      let (indexed, aux) = assigned_map in
                                                                                                                      (Assignment (xs @ [(x, true, true, dl + 1)]), (Assignment_Map.add y true indexed, aux), f_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                                      (*else let (new_map, new_state, prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Atom (x)) in
                                                                                                                       (Assignment (xs @ [(x, false, false, dl)]), new_map, dl, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), new_state, prop, conf, false)*)
                                                                                                | Inr (n_state) -> let (indexed, aux) = assigned_map in
                                                                                                                    let new_assigned_map = (Assignment_Map.add y true indexed, aux) in
                                                                                                                     let (new_map, prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Not (Atom (x))) in 
                                                                                                                        (Assignment (xs @ [(x, true, true, dl + 1)]), new_assigned_map, new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                                           )   
                                                                        )
                                                                    else (
                                                                          let AuxVar (y) = x in 
                                                                           let (indexed, aux) = assigned_map in
                                                                            let new_assigned_map = (indexed, Assignment_Map.add y true aux) in
                                                                             let (new_map, prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Not (Atom (x))) in 
                                                                                 (Assignment (xs @ [(x, true, true, dl + 1)]), new_assigned_map, new_map, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, prop, conf, false)
                                                                        )
                                                        | [Not (Atom (x))] -> (*printf "decision literal: Not %s\n\n" (Printing.print_constraint_n x);*) 
                                                                            if is_proper_constraint x
                                                                            then (
                                                                                  match x with
                                                                                    | Constraint (y) -> (
                                                                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n x) i_map))) s_state with
                                                                                                            | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), assigned_map, f_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                            | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists_i assignment assigned_map f_map (Atom (x)) in 
                                                                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), assigned_map, new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                                                        )
                                                                                    | Index (y) -> (
                                                                                                    let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in 
                                                                                                    (*printf ("decision, not atom: %s\n") (Printing.print_constraint_n c);*)
                                                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map))) s_state with
                                                                                                        | Inl (unsat_core) -> (*printf "unsat_core\n";*) 
                                                                                                                             (*if true 
                                                                                                                             then*) 
                                                                                                                             let (indexed, aux) = assigned_map in
                                                                                                                             (Assignment (xs @ [(x, false, true, dl + 1)]), (Assignment_Map.add y false indexed, aux), f_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                                                                             (*else let (new_map, new_state, prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Not (Atom (x))) in
                                                                                                                                (Assignment (xs @ [(x, true, false, dl)]), new_map, dl, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), new_state, prop, conf, false)*)
                                                                                                        | Inr (n_state) -> let (indexed, aux) = assigned_map in
                                                                                                                            let new_assigned_map = (Assignment_Map.add y false indexed, aux) in
                                                                                                                             let (new_map, prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Atom (x)) in 
                                                                                                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_assigned_map, new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                                                   )
                                                                                )
                                                                            else (
                                                                                  let AuxVar (y) = x in 
                                                                                   let (indexed, aux) = assigned_map in
                                                                                    let new_assigned_map = (indexed, Assignment_Map.add y false aux) in
                                                                                     let (new_map, prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Atom (x)) in
                                                                                      (Assignment (xs @ [(x, false, true, dl + 1)]), new_assigned_map, new_map, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, prop, conf, false) 
                                                                                )
                                                        | _ -> failwith "[Invalid argument] decision_twl_inc: choose_decision_literal did not return a literal"
                                                )
                                     (*)*)
     | _ -> failwith "[Invalid argument] decision_twl_inc: formula not in CNF";;

let rec unit_propagation_twl_inc assignment f_map s_state i_map inv_map prop dl = 
    (*printf "PROPAGATION\n\n";*) match prop with 
        | [] -> (assignment, f_map, s_state, [])
        | x :: xs -> (
                      let Assignment (ys) = assignment in 
                       match x with
                        | Atom (y) -> if is_proper_constraint y 
                                      then (
                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))) s_state with
                                                | Inl (unsat_core) -> (assignment, f_map, s_state, convert_unsat_core (unsat_core) inv_map)
                                                | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Not (Atom (y))) in 
                                                                    (
                                                                    match conf with 
                                                                        | [] -> unit_propagation_twl_inc (Assignment (ys @ [(y, true, false, dl)])) new_map n_state i_map inv_map (xs @ new_prop) dl
                                                                        | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_map, s_state, z :: zs)
                                                                    )
                                            )
                                      else (
                                            let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Not (Atom (y))) in 
                                            (
                                            match conf with 
                                                | [] -> unit_propagation_twl_inc (Assignment (ys @ [(y, true, false, dl)])) new_map s_state i_map inv_map (xs @ new_prop) dl
                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_map, s_state, z :: zs)
                                            )
                                           )
                        | Not (Atom (y)) -> if is_proper_constraint y 
                                                then (
                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n y)) i_map))) s_state with
                                                            | Inl (unsat_core) -> (assignment, f_map, s_state, convert_unsat_core (unsat_core) inv_map)
                                                            | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Atom (y)) in 
                                                                                ( 
                                                                                match conf with
                                                                                    | [] -> unit_propagation_twl_inc (Assignment (ys @ [(y, false, false, dl)])) new_map n_state i_map inv_map (xs @ new_prop) dl
                                                                                    | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_map, s_state, z :: zs)
                                                                                )
                                                        )
                                                else (
                                                      let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Atom (y)) in 
                                                        ( 
                                                        match conf with
                                                            | [] -> unit_propagation_twl_inc (Assignment (ys @ [(y, false, false, dl)])) new_map s_state i_map inv_map (xs @ new_prop) dl
                                                            | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_map, s_state, z :: zs)
                                                        )
                                                    )
                        | _ -> failwith "[Invalid argument] unit_propagation_twl: list of propagation literals contains a non-literal element"
                     );;

(*let rec unit_propagation_twl_inc_i assignment f_map up_map s_state i_map inv_map prop dl = 
    (*printf "PROPAGATION\n"; *)
    (* printf "prop: %s\n" (Printing.print_element_list prop);*) match prop with 
        | [] -> (assignment, f_map, up_map, s_state, [])
        | up_pair :: xs -> (
                      let Assignment (ys) = assignment in 
                      let (x, clause) = up_pair in
                       match x with
                        | Atom (y) -> if is_proper_constraint y 
                                      then (
                                            match y with 
                                                | Constraint (z) -> (
                                                                     match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))) s_state with
                                                                        | Inl (unsat_core) -> (* TODO: is distinction between u-core and regular conf necessary? *) 
                                                                                             (Assignment (ys @ [(y, true, false, dl)]), f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                        | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (y))) in 
                                                                                            (
                                                                                            match conf with 
                                                                                                | [] -> unit_propagation_twl_inc_i (Assignment (ys @ [(y, true, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                            )
                                                                    )
                                                | Index (z) -> (
                                                                let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find z inv_map) in
                                                                (*printf ("atom: %s\n") (Printing.print_constraint_n s);*) match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int z)) s_state with
                                                                        | Inl (unsat_core) -> (*printf "unsat_core\n";*)
                                                                                             (*let (new_map, new_state, new_prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Not (Atom (y))) in
                                                                                                                       (Assignment (ys @ [(y, false, false, dl)]), new_map, (UP_Map.add (Printing.print_element (Not (Atom (y)))) (Disjunction ([])) up_map), new_state, conf)*)
                                                                                             (Assignment (ys @ [(y, true, false, dl)]), f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                        | Inr (n_state) -> (*printf "state\n";*) let (new_map, new_prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (y))) in 
                                                                                            (
                                                                                            match conf with 
                                                                                                | [] -> if dl < 1 
                                                                                                        then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i (Assignment (ys @ [(y, true, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl)
                                                                                                        else unit_propagation_twl_inc_i (Assignment (ys @ [(y, true, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                | z :: zs -> if dl < 1
                                                                                                             then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, true, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf))
                                                                                                             else ((Assignment (ys @ [(y, true, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                            )
                                                               )
                                            )
                                      else (
                                            let (new_map, new_prop, conf) = update_watch_lists_i assignment f_map (Not (Atom (y))) in 
                                            (
                                            match conf with 
                                                | [] -> if dl < 1 
                                                        then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i (Assignment (ys @ [(y, true, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl)
                                                        else unit_propagation_twl_inc_i (Assignment (ys @ [(y, true, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl
                                                | z :: zs -> if dl < 1
                                                             then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, true, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf))
                                                             else ((Assignment (ys @ [(y, true, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                            )
                                           )
                        | Not (Atom (y)) -> if is_proper_constraint y 
                                                then (
                                                      match y with
                                                        | Constraint (z) -> (
                                                                             match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n y)) i_map))) s_state with
                                                                                | Inl (unsat_core) -> (Assignment (ys @ [(y, false, false, dl)]), f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                                | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists_i assignment f_map (Atom (y)) in 
                                                                                                    ( 
                                                                                                    match conf with
                                                                                                        | [] -> unit_propagation_twl_inc_i (Assignment (ys @ [(y, false, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                        | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                                    )
                                                                            )
                                                        | Index (z) -> (
                                                                        (*printf "z: %s\n" (string_of_int z);*)
                                                                        let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find z inv_map) in 
                                                                        (*printf ("up, not atom: %s, index: %s\n") (Printing.print_constraint_n c) (string_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map));
                                                                        printf ("up, not atom: %s, index: %s\n") ("-" ^ (Printing.print_constraint_n c)) (string_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map));*)
                                                                        (*let (bla0, v0, d0, tmpdl0) = (Tseitin.Inv_Map.find 0 inv_map) in 
                                                                         let (bla1, v1, d1, tmpdl1) = (Tseitin.Inv_Map.find 1 inv_map) in
                                                                          printf ("index 0 cons: %s\n") (Printing.print_constraint_n bla0);
                                                                          printf ("index 1 cons: %s\n") (Printing.print_constraint_n bla1);*)
                                                                         match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) s_state with
                                                                            | Inl (unsat_core) -> (*printf "unsat_core\n"; *)
                                                                                                    (*let (new_map, new_state, new_prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Atom (y)) in
                                                                                                                       (Assignment (ys @ [(y, true, false, dl)]), new_map, (UP_Map.add (Printing.print_element (Atom (y))) (Disjunction ([])) up_map), new_state, conf)*)
                                                                                                    (Assignment (ys @ [(y, false, false, dl)]), f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                            | Inr (n_state) -> (*printf "state\n";*) let (new_map, new_prop, conf) = update_watch_lists_i assignment f_map (Atom (y)) in 
                                                                                                ( 
                                                                                                 match conf with
                                                                                                    | [] -> if dl < 1 
                                                                                                            then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i (Assignment (ys @ [(y, false, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl)
                                                                                                            else unit_propagation_twl_inc_i (Assignment (ys @ [(y, false, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                    | z :: zs -> if dl < 1
                                                                                                                 then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, false, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf))
                                                                                                                 else ((Assignment (ys @ [(y, false, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                                )
                                                                       )
                                                     )
                                                else (
                                                      let (new_map, new_prop, conf) = update_watch_lists_i assignment f_map (Atom (y)) in 
                                                        ( 
                                                        match conf with
                                                            | [] -> if dl < 1
                                                                    then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i (Assignment (ys @ [(y, false, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl)
                                                                    else unit_propagation_twl_inc_i (Assignment (ys @ [(y, false, false, dl)])) new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl
                                                            | z :: zs -> if dl < 1
                                                                         then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, false, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, z :: zs))
                                                                         else ((Assignment (ys @ [(y, false, false, dl)])), new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                        )
                                                    )
                        | _ -> failwith "[Invalid argument] unit_propagation_twl: list of propagation literals contains a non-literal element"
                     );;*)

let rec unit_propagation_twl_inc_i_map assignment assigned_map f_map up_map s_state i_map inv_map prop dl = 
    (*printf "PROPAGATION\n"; *)
    (* printf "prop: %s\n" (Printing.print_element_list prop);*) match prop with 
        | [] -> (assignment, assigned_map, f_map, up_map, s_state, [])
        | up_pair :: xs -> (
                      let Assignment (ys) = assignment in 
                      let (x, clause) = up_pair in
                       match x with
                        | Atom (y) -> if is_proper_constraint y 
                                      then (
                                            match y with 
                                                | Constraint (z) -> (
                                                                     match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))) s_state with
                                                                        | Inl (unsat_core) -> (* TODO: is distinction between u-core and regular conf necessary? *) 
                                                                                             (Assignment (ys @ [(y, true, false, dl)]), assigned_map, f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                        | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists_i assignment assigned_map f_map (Not (Atom (y))) in 
                                                                                            (
                                                                                            match conf with 
                                                                                                | [] -> unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, true, false, dl)])) assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                            )
                                                                    )
                                                | Index (z) -> (
                                                                let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find z inv_map) in
                                                                (*printf ("atom: %s\n") (Printing.print_constraint_n s);*) match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int z)) s_state with
                                                                        | Inl (unsat_core) -> (*printf "unsat_core\n";*)
                                                                                             (*let (new_map, new_state, new_prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Not (Atom (y))) in
                                                                                                                       (Assignment (ys @ [(y, false, false, dl)]), new_map, (UP_Map.add (Printing.print_element (Not (Atom (y)))) (Disjunction ([])) up_map), new_state, conf)*)
                                                                                             let (indexed, aux) = assigned_map in
                                                                                             (Assignment (ys @ [(y, true, false, dl)]), (Assignment_Map.add z true indexed, aux), f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                        | Inr (n_state) -> let (indexed, aux) = assigned_map in
                                                                                            let new_assigned_map = (Assignment_Map.add z true indexed, aux) in
                                                                                            let (new_map, new_prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Not (Atom (y))) in 
                                                                                            (
                                                                                            match conf with 
                                                                                                | [] -> if dl < 1 
                                                                                                        then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, true, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl)
                                                                                                        else unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, true, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                | z :: zs -> if dl < 1
                                                                                                             then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, true, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf))
                                                                                                             else ((Assignment (ys @ [(y, true, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                            )
                                                               )
                                            )
                                      else (
                                            let AuxVar (z) = y in
                                            let (indexed, aux) = assigned_map in
                                            let new_assigned_map = (indexed, Assignment_Map.add z true aux) in
                                            let (new_map, new_prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Not (Atom (y))) in 
                                            (
                                            match conf with 
                                                | [] -> if dl < 1 
                                                        then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, true, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl)
                                                        else unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, true, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl
                                                | z :: zs -> if dl < 1
                                                             then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, true, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf))
                                                             else ((Assignment (ys @ [(y, true, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                            )
                                           )
                        | Not (Atom (y)) -> if is_proper_constraint y 
                                                then (
                                                      match y with
                                                        | Constraint (z) -> (
                                                                             match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n y)) i_map))) s_state with
                                                                                | Inl (unsat_core) -> (Assignment (ys @ [(y, false, false, dl)]), assigned_map, f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                                | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists_i assignment assigned_map f_map (Atom (y)) in 
                                                                                                    ( 
                                                                                                    match conf with
                                                                                                        | [] -> unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, false, false, dl)])) assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                        | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                                    )
                                                                            )
                                                        | Index (z) -> (
                                                                        (*printf "z: %s\n" (string_of_int z);*)
                                                                        let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find z inv_map) in 
                                                                        (*printf ("up, not atom: %s, index: %s\n") (Printing.print_constraint_n c) (string_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map));
                                                                        printf ("up, not atom: %s, index: %s\n") ("-" ^ (Printing.print_constraint_n c)) (string_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map));*)
                                                                        (*let (bla0, v0, d0, tmpdl0) = (Tseitin.Inv_Map.find 0 inv_map) in 
                                                                         let (bla1, v1, d1, tmpdl1) = (Tseitin.Inv_Map.find 1 inv_map) in
                                                                          printf ("index 0 cons: %s\n") (Printing.print_constraint_n bla0);
                                                                          printf ("index 1 cons: %s\n") (Printing.print_constraint_n bla1);*)
                                                                         match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) s_state with
                                                                            | Inl (unsat_core) -> (*printf "unsat_core\n"; *)
                                                                                                    (*let (new_map, new_state, new_prop, conf) = t_propagation_i assignment f_map s_state i_map inv_map (Atom (y)) in
                                                                                                                       (Assignment (ys @ [(y, true, false, dl)]), new_map, (UP_Map.add (Printing.print_element (Atom (y))) (Disjunction ([])) up_map), new_state, conf)*)
                                                                                                    let (indexed, aux) = assigned_map in
                                                                                                    (Assignment (ys @ [(y, false, false, dl)]), (Assignment_Map.add z false indexed, aux), f_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                            | Inr (n_state) -> let (indexed, aux) = assigned_map in
                                                                                               let new_assigned_map = (Assignment_Map.add z false indexed, aux) in
                                                                                               let (new_map, new_prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Atom (y)) in 
                                                                                                ( 
                                                                                                 match conf with
                                                                                                    | [] -> if dl < 1 
                                                                                                            then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, false, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl)
                                                                                                            else unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, false, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                    | z :: zs -> if dl < 1
                                                                                                                 then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, false, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf))
                                                                                                                 else ((Assignment (ys @ [(y, false, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                                )
                                                                       )
                                                     )
                                                else (
                                                      let AuxVar (z) = y in
                                                      let (indexed, aux) = assigned_map in
                                                      let new_assigned_map = (indexed, Assignment_Map.add z false aux) in
                                                      let (new_map, new_prop, conf) = update_watch_lists_i assignment new_assigned_map f_map (Atom (y)) in 
                                                        ( 
                                                        match conf with
                                                            | [] -> if dl < 1
                                                                    then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, false, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl)
                                                                    else unit_propagation_twl_inc_i_map (Assignment (ys @ [(y, false, false, dl)])) new_assigned_map new_map (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl
                                                            | z :: zs -> if dl < 1
                                                                         then ((*printf "propagated: %s at level %s\n\n" (Printing.print_element x) (string_of_int dl);*) ((Assignment (ys @ [(y, false, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, z :: zs))
                                                                         else ((Assignment (ys @ [(y, false, false, dl)])), new_assigned_map, new_map, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                        )
                                                    )
                        | _ -> failwith "[Invalid argument] unit_propagation_twl: list of propagation literals contains a non-literal element"
                     );;

let rec reassert_after_restart_rec assignment i_map inv_map state conf to_update = 
    match assignment with
        | Assignment ([]) -> (state, conf, to_update)
        | Assignment ((c, v, d, dl) :: xs) -> (
                                               match c with
                                                | AuxVar (x) -> (
                                                                 match v with
                                                                    | true -> reassert_after_restart_rec (Assignment (xs)) i_map inv_map state conf (to_update @ [(Not (Atom (c)))])
                                                                    | false -> reassert_after_restart_rec (Assignment (xs)) i_map inv_map state conf (to_update @ [(Atom (c))])
                                                                ) 
                                                | Index (x) -> (
                                                                match v with
                                                                    | true -> (
                                                                               match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int x)) state with
                                                                                | Inl (unsat_core) -> (state, unsat_core, to_update)
                                                                                | Inr (new_state) -> reassert_after_restart_rec (Assignment (xs)) i_map inv_map new_state conf (to_update @ [(Not (Atom (c)))])
                                                                              )
                                                                    | false -> let (s, _, _, _) = (Tseitin.Inv_Map.find x inv_map) in
                                                                                (
                                                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n s)) i_map))) state with  
                                                                                 | Inl (unsat_core) -> (state, unsat_core, to_update)
                                                                                 | Inr (new_state) -> reassert_after_restart_rec (Assignment (xs)) i_map inv_map new_state conf (to_update @ [(Atom (c))])
                                                                                )
                                                               )
                                                | Constraint (x) -> (
                                                                     match v with
                                                                        | true -> (
                                                                                   match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map))) state with
                                                                                    | Inl (unsat_core) -> (state, unsat_core, to_update)
                                                                                    | Inr (new_state) -> reassert_after_restart_rec (Assignment (xs)) i_map inv_map new_state conf (to_update @ [(Not (Atom (c)))])
                                                                                  )
                                                                        | false -> (
                                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) state with  
                                                                                    | Inl (unsat_core) -> (state, unsat_core, to_update)
                                                                                    | Inr (new_state) -> reassert_after_restart_rec (Assignment (xs)) i_map inv_map new_state conf  (to_update @ [(Atom (c))])
                                                                                   )
                                                                    )
                                                | _ -> failwith "[Invalid argument] reassert_after_restart_rec: non indexed constraints used with index version of function"
                                              ) 
        | _ -> failwith "[Invalid argument] reassert_after_restart_rec";;


let reassert_after_restart assignment i_map inv_map state = (* printf "REASSERT\n";*) reassert_after_restart_rec assignment i_map inv_map state [] [];;

let rec assert_list_rec assignment list i_map inv_map state conf dl = 
    match list with 
        | [] -> (assignment, state, conf)
        | (c, v, d, _) :: xs -> (
                                  if is_proper_constraint c 
                                  then (
                                        match c with 
                                            | Index (x) -> (
                                                            match v with 
                                                                | true -> (
                                                                           match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int x)) state with
                                                                            | Inl (unsat_core) -> (assignment, state, unsat_core)
                                                                            | Inr (new_state) -> assert_list_rec (assignment @ [(c, v, d, dl)]) xs i_map inv_map new_state conf dl
                                                                          )
                                                                | false -> let (s, _, _, _) = (Tseitin.Inv_Map.find x inv_map) in
                                                                          (
                                                                           match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n s)) i_map))) state with  
                                                                            | Inl (unsat_core) -> (assignment, state, unsat_core)
                                                                            | Inr (new_state) -> assert_list_rec (assignment @ [(c, v, d, dl)]) xs i_map inv_map new_state conf dl
                                                                          )
                                                           )
                                            | Constraint (x) -> (
                                                                 match v with
                                                                    | true -> (
                                                                               match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map))) state with
                                                                                | Inl (unsat_core) -> (assignment, state, unsat_core)
                                                                                | Inr (new_state) -> assert_list_rec (assignment @ [(c, v, d, dl)]) xs i_map inv_map new_state conf dl
                                                                              )
                                                                    | false -> (
                                                                                match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) state with  
                                                                                    | Inl (unsat_core) -> (assignment, state, unsat_core)
                                                                                    | Inr (new_state) -> assert_list_rec (assignment @ [(c, v, d, dl)]) xs i_map inv_map new_state conf dl
                                                                               )
                                                                )
                                       )
                                  else assert_list_rec (assignment @ [(c, v, d, dl)]) xs i_map inv_map state conf dl
                                 )
        | _ -> failwith "[Invalid argument] assert_list_rec";;

let assert_list assignment list i_map inv_map state = assert_list_rec assignment list i_map inv_map state [];;

let assert_backjump l i_map inv_map state = 
    match l with 
        | Atom (x) -> if (is_proper_constraint x)
                      then (
                            match x with
                                | Index (y) -> let (c, v, d, dl) = (Tseitin.Inv_Map.find y inv_map) in
                                                (
                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) state with
                                                    | Inl (unsat_core) -> (state, unsat_core)
                                                    | Inr (n_state) -> (
                                                                        match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                            | Inl (n_unsat_core) -> (n_state, n_unsat_core)
                                                                            | Inr (new_state) -> (new_state, [])
                                                                       )
                                                )
                                | Constraint (y) -> (
                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n x)) i_map))) state with
                                                        | Inl (unsat_core) -> (state, unsat_core)
                                                        | Inr (n_state) -> (
                                                                            match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                                | Inl (n_unsat_core) -> (n_state, n_unsat_core)
                                                                                | Inr (new_state) -> (new_state, [])
                                                                           )
                                                    )
                                | _ -> failwith "[Invalid argument] assert_backjump"
                            )
                      else (state, [])
        | Not (Atom (x)) -> if (is_proper_constraint x)
                            then (
                                  match x with
                                    | Index (y) -> (
                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int y)) state with
                                                        | Inl (unsat_core) -> (state, unsat_core)
                                                        | Inr (n_state) -> (
                                                                            match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                                | Inl (n_unsat_core) -> (n_state, n_unsat_core)
                                                                                | Inr (new_state) -> (new_state, [])
                                                                           )
                                                   )
                                    | Constraint (y) -> (
                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map))) state with
                                                        | Inl (unsat_core) -> (state, unsat_core)
                                                        | Inr (n_state) -> (
                                                                            match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                                | Inl (n_unsat_core) -> (n_state, n_unsat_core)
                                                                                | Inr (new_state) -> (new_state, [])
                                                                           )
                                                   )
                                    | _ -> failwith "[Invalid argument] assert_backjump"
                                 )
                            else (state, [])
        | _ -> failwith "[Invalid argument] assert_backjump";;

(* Since target decision level bj_dl for backjump is theory inconsistent we 
   need to find the next largest decision level for backjumping that is 
   consistent. That basically means doing a backjump to the first UIP
   and then using simple backtrack to reach a consistent state afterwards. *)
let rec backjump_to_t_consistent_state_rec assignment assignment_mutable up_map checkpoints i_map inv_map bj_dl state result =
    match (assignment_mutable, bj_dl) with
        | (Assignment ([]), _) -> failwith "[Invalid argument] backjump_to_t_consistent_state_rec: target decision level too high"
        | (Assignment (_), 1) -> ([], up_map, checkpoints, state, 0, Atom (AuxVar (-1)))
        | (Assignment (_), 0) -> ([], up_map, checkpoints, state, 0, Atom (AuxVar (-1)))
        | (Assignment ((c, v, d, dl) :: xs), _) -> if dl = (bj_dl - 1)
                                                   then let tmp_state = Simplex_inc.backtrack_simplex (get_checkpoint checkpoints (dl - 1)) state in
                                                   (
                                                    if (is_proper_constraint c) 
                                                    then (
                                                          match (v, c) with
                                                            | (true, Index (x)) -> let (xc, xv, xd, xdl) = (Tseitin.Inv_Map.find x inv_map) in
                                                                                    (
                                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n xc)) i_map))) tmp_state with
                                                                                        | Inl (unsat_core) -> backjump_to_t_consistent_state_rec assignment assignment up_map checkpoints i_map inv_map (bj_dl - 1) state []
                                                                                        | Inr (n_state) -> (result @ [(c, false, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), n_state, (dl - 1), Atom (c))
                                                                                    )
                                                            | (false, Index (x)) -> (
                                                                                    match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int x)) tmp_state with
                                                                                        | Inl (unsat_core) -> backjump_to_t_consistent_state_rec assignment assignment up_map checkpoints i_map inv_map (bj_dl - 1) state []
                                                                                        | Inr (n_state) -> (result @ [(c, true, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), n_state, (dl - 1), Not (Atom (c)))
                                                                                    )
                                                            | (true, Constraint (x)) -> (
                                                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) tmp_state with
                                                                                            | Inl (unsat_core) -> backjump_to_t_consistent_state_rec assignment assignment up_map checkpoints i_map inv_map (bj_dl - 1) state []
                                                                                            | Inr (n_state) -> (result @ [(c, false, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), n_state, (dl - 1), Atom (c))
                                                                                        )
                                                            | (false, Constraint (x)) -> (
                                                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map))) tmp_state with
                                                                                            | Inl (unsat_core) -> backjump_to_t_consistent_state_rec assignment assignment up_map checkpoints i_map inv_map (bj_dl - 1) state []
                                                                                            | Inr (n_state) -> (result @ [(c, true, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), n_state, (dl - 1), Not (Atom (c)))
                                                                                        )
                                                            | _ -> failwith "[Invalid argument] backjump_to_t_consistent_state_rec"
                                                         )
                                                    else (
                                                          match v with
                                                            | true -> (result @ [(c, false, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), tmp_state, (dl - 1), Atom (c))
                                                            | false -> (result @ [(c, true, false, dl - 1)], up_map, (reset_checkpoints checkpoints (dl - 1)), tmp_state, (dl - 1), Not (Atom (c)))
                                                         )
                                                   )
                                                   else backjump_to_t_consistent_state_rec assignment (Assignment (xs)) up_map checkpoints i_map inv_map bj_dl state (result @ [(c, v, d, dl)]);;

let backjump_to_t_consistent_state assignment up_map checkpoints i_map inv_map dl state = (*printf "BJ_T_CONS\n\n";*) backjump_to_t_consistent_state_rec assignment assignment up_map checkpoints i_map inv_map dl state [];;

let rec dpll_twl_inc_rec assignment formula f_map up_map s_state checkpoints i_map inv_map dl = 
    (*Printing.print_assignment assignment; printf "\n\n";*) match model_found_twl assignment formula with
        | true -> (
                   (*Printing.print_assignment assignment; printf "\n\n";*) (*Printing.print_simplex_constraints sf_assignment;*) 
                   match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) s_state with
                    | Simplex_inc.Inl (unsat_core) -> if dl < 1
                                                      then false
                                                      else let (num, cp) = hd (checkpoints) in
                                                            let r_state = Simplex_inc.backtrack_simplex cp s_state in
                                                            let ys = clauselist_to_neg_clause (convert_unsat_core unsat_core inv_map) in 
                                                                (*printf "restart\n\n";*)
                                                                restart_twl_inc assignment (learn formula ys) (add_clause_to_map f_map ys) up_map r_state [hd (checkpoints)] i_map inv_map
                    | Simplex_inc.Inr (n_state) -> (* According to my understanding this is sufficient info to determine that formula is SAT *)
                                                    (* Printing.print_assignment assignment; *) true
                  )
        | false -> let new_cps = checkpoints @ [(dl, Simplex_inc.checkpoint_simplex s_state)] in
                    let (new_assignment, new_map, new_dl, new_state, prop, conf) = decision_twl_inc formula assignment f_map s_state i_map inv_map dl in 
                    (
                     match conf with 
                        | [] -> (
                                 match prop with
                                    | [] -> dpll_twl_inc_rec new_assignment formula new_map up_map new_state new_cps i_map inv_map new_dl
                                    | x :: xs -> let (n_assignment, n_map, n_state, n_conf) = unit_propagation_twl_inc new_assignment new_map new_state i_map inv_map prop new_dl in 
                                                    (
                                                     match n_conf with
                                                      | [] -> (
                                                                match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                    | Inl (unsat_core) -> let (num, cp) = hd (checkpoints) in
                                                                                          let r_state = Simplex_inc.backtrack_simplex cp n_state in
                                                                                          (
                                                                                           match length unsat_core with 
                                                                                            | 0 -> failwith "[Invalid argument] unsat core empty"
                                                                                            | 1 -> (
                                                                                                    match (hd (convert_unsat_core unsat_core inv_map)) with
                                                                                                        | Atom (y) -> restart_twl_inc_unit n_assignment formula f_map up_map r_state [hd (checkpoints)] i_map inv_map y false
                                                                                                        | Not (Atom (y)) -> restart_twl_inc_unit n_assignment formula f_map up_map r_state [hd (checkpoints)] i_map inv_map y true
                                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: unsat_core does not consist of literals"
                                                                                                   )
                                                                                            | _ -> let ys = clauselist_to_neg_clause (convert_unsat_core unsat_core inv_map) in 
                                                                                                    (*printf "restart\n\n";*) restart_twl_inc assignment (learn formula ys) (add_clause_to_map n_map ys) up_map r_state [hd (checkpoints)] i_map inv_map
                                                                                          )
                                                                    | Inr (state) -> dpll_twl_inc_rec n_assignment formula n_map up_map state new_cps i_map inv_map new_dl
                                                               )
                                                      | x :: xs -> (
                                                                    let (ys, l, bj_clause) = (backjump_twl n_assignment formula (hd n_conf)) in 
                                                                    let (bj_map, _, _) = update_watch_lists ys new_map l in
                                                                     let cdl = (get_current_decision_level ys) in
                                                                      let cp = get_checkpoint new_cps cdl in 
                                                                       let b_state = Simplex_inc.backtrack_simplex cp n_state in 
                                                                        let (bj_state, unsat_core) = assert_backjump l i_map inv_map b_state in
                                                                         (
                                                                          match (length unsat_core) with
                                                                            | 0 -> (
                                                                                    (*printf "BACKJUMP\n\n";*) match (bj_clause, (conflict_exists ys formula)) with
                                                                                        | (_, true) -> false
                                                                                        | (Disjunction ([]), false) -> dpll_twl_inc_rec ys formula bj_map up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl
                                                                                        | (Disjunction ([v]), false) -> dpll_twl_inc_rec ys formula bj_map up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl
                                                                                        | (Disjunction (vs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_inc_rec ys formula_l (add_clause_to_map bj_map bj_clause) up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl
                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                   )
                                                                            | _ -> (
                                                                                    match backjump_to_t_consistent_state ys up_map new_cps i_map inv_map cdl b_state with 
                                                                                     | ([], _, _, _, _, _) -> false
                                                                                     | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) -> let (cons_map, _, _) = update_watch_lists (Assignment (cons_assignment)) new_map cons_l in
                                                                                                                                          dpll_twl_inc_rec (Assignment (cons_assignment)) formula cons_map cons_up_map cons_state cons_cps i_map inv_map cons_dl
                                                                                   )

                                                                         )
                                                                   )
                                                    )
                                )
                        | x :: xs -> (
                                      let (ys, l, bj_clause) = (backjump_twl new_assignment formula (hd conf)) in 
                                      let (bj_map, _, _) = update_watch_lists ys new_map l in
                                       let cdl = (get_current_decision_level ys) in
                                        let cp = get_checkpoint new_cps cdl in 
                                         let b_state = Simplex_inc.backtrack_simplex cp new_state in 
                                          let (bj_state, unsat_core) = assert_backjump l i_map inv_map b_state in
                                            (
                                             match (length unsat_core) with
                                                | 0 -> (
                                                        (*printf "BACKJUMP\n\n";*) match (bj_clause, (conflict_exists ys formula)) with
                                                        | (_, true) -> false
                                                        | (Disjunction ([]), false) -> dpll_twl_inc_rec ys formula bj_map up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl
                                                        | (Disjunction ([v]), false) -> dpll_twl_inc_rec ys formula bj_map up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl
                                                        | (Disjunction (vs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_inc_rec ys formula_l (add_clause_to_map bj_map bj_clause) up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl
                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                        )
                                                | _ -> (
                                                        match backjump_to_t_consistent_state ys up_map new_cps i_map inv_map cdl b_state with 
                                                        | ([], _, _, _, _, _) -> false
                                                        | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) -> let (cons_map, _, _) = update_watch_lists (Assignment (cons_assignment)) new_map cons_l in
                                                                                                                    dpll_twl_inc_rec (Assignment (cons_assignment)) formula cons_map cons_up_map cons_state cons_cps i_map inv_map cons_dl
                                                      )
                                            )
                                     )
                                      
                    )

and dpll_twl_inc formula up_map i_map inv_map s_state checkpoints = 
                let (new_formula, new_assignment, prop, conf_unit, new_state, to_update) = preprocess_unit_clauses_inc (Assignment ([])) formula s_state i_map inv_map in 
                        (*Printing.print_formula new_formula; printf "\n\n";*) 
                        if conf_unit 
                        then false
                        else (
                              let (f_map, literals) = construct_map new_formula in 
                               let (f_map_new, prop_new, conf_new) = update_watch_lists_l new_assignment f_map to_update in
                                let (n_assignment, n_map, n_state, conf) = unit_propagation_twl_inc new_assignment f_map new_state i_map inv_map prop 0 in 
                                    (
                                     match conf with
                                        | [] -> dpll_twl_inc_rec n_assignment new_formula up_map n_map n_state checkpoints i_map inv_map 0
                                        | x :: xs -> false
                                    )
                            )

and restart_twl_inc assignment formula f_map up_map s_state checkpoints i_map inv_map = 
                        let (new_formula, new_assignment, prop, conf_unit, new_state, to_update) = preprocess_unit_clauses_inc (preserve_unit_assignments assignment) formula s_state i_map inv_map in 
                            if conf_unit
                            then false
                            else (
                                  let (ra_state, ra_conf, ra_to_update) = reassert_after_restart new_assignment i_map inv_map new_state in
                                    (
                                     if length ra_conf > 0
                                     then false
                                     else (
                                           let (f_map_new, prop_new, conf_new) = update_watch_lists_l new_assignment f_map (to_update @ ra_to_update) in
                                            let (n_assignment, n_map, n_state, conf) = unit_propagation_twl_inc new_assignment f_map ra_state i_map inv_map prop 0 in 
                                                (
                                                match conf with
                                                    | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) 
                                                        dpll_twl_inc_rec n_assignment new_formula n_map up_map n_state checkpoints i_map inv_map 0
                                                    | x :: xs -> false
                                                )
                                          )
                                    )
                                 )
                                                
and restart_twl_inc_unit assignment formula f_map up_map s_state checkpoints i_map inv_map unit_literal lit_val = 
                        let (new_formula, new_assignment, prop, conf_unit, new_state, to_update) = preprocess_unit_clauses_inc (preserve_unit_assignments assignment) formula s_state i_map inv_map in
                            if conf_unit
                            then false
                            else (
                                let (ra_state, ra_conf, ra_to_update) = reassert_after_restart new_assignment i_map inv_map new_state in
                                    (
                                     if length ra_conf > 0
                                     then false
                                     else (
                                           let (f_map_new, prop_new, conf_new) = update_watch_lists_l new_assignment f_map (to_update @ ra_to_update) in
                                            let Assignment (xs) = new_assignment in 
                                            if (is_assigned new_assignment (Atom (unit_literal)))
                                            then false
                                            else let (n_assignment, n_map, n_state, conf) = unit_propagation_twl_inc (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) f_map ra_state i_map inv_map prop 0 in 
                                                    (
                                                    match conf with
                                                        | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) 
                                                                dpll_twl_inc_rec n_assignment new_formula n_map up_map n_state checkpoints i_map inv_map  0
                                                        | x :: xs -> false
                                                    )
                                          )
                                    )
                                 );;

let compare_vsids vsids_p1 vsids_p2 =
    match (vsids_p1, vsids_p2) with
     | ((l1, v1), (l2, v2)) -> compare v1 v2;;

let rec update_vsids vsids_pair clause = 
    match (vsids_pair, clause) with 
     | ((lit, v), Disjunction ([])) -> (lit, v *. 0.5)
     | ((lit, v), Disjunction (x :: xs)) -> (
                                             match x with 
                                                | Not (Atom (y)) -> (
                                                                     match compare lit (Atom (y)) with 
                                                                      | 0 -> (lit, (v *. 0.5) +. 10.0)
                                                                      | _ -> update_vsids vsids_pair (Disjunction (xs))
                                                                    )
                                                | Atom (y) -> (
                                                               match compare lit x with 
                                                                | 0 -> (lit, (v *. 0.5) +. 10.0)
                                                                | _ -> update_vsids vsids_pair (Disjunction (xs))
                                                              )
                                            );;

let rec decay_and_update_vsids_rec vsids clause result =
    match vsids with 
     | [] -> result
     | (lit, v) :: vs ->  let n_vsids_pair = update_vsids (lit, v) clause in
                            decay_and_update_vsids_rec vs clause (result @ [n_vsids_pair]);;

let decay_and_update_vsids vsids learned_clause = decay_and_update_vsids_rec vsids learned_clause [];;

let rec reconstruct_assigned_map_rec assignment assigned_map = 
    match assignment with
        | Assignment ([]) -> assigned_map
        | Assignment ((c, v, d, dl) :: xs) -> (
                                               match c with 
                                                | Index (x) -> let (indexed, aux) = assigned_map in 
                                                                reconstruct_assigned_map_rec (Assignment (xs)) ((Assignment_Map.add x v indexed), aux)
                                                | AuxVar (x) -> let (indexed, aux) = assigned_map in 
                                                                reconstruct_assigned_map_rec (Assignment (xs)) (indexed, (Assignment_Map.add x v aux))
                                                | _ -> failwith "[Invalid argument] reconstruct_assigned_map_rec: assigned variable is not indexed and not an auxiliary variable"
                                              );; 

let reconstruct_assigned_map assignment = reconstruct_assigned_map_rec assignment (Assignment_Map.empty, Assignment_Map.empty);;

let rec backjump_cdcl formula assignment f_map up_map checkpoints dl conf i_map inv_map state = 
    let (xs, l, bj_clause, bj_up_map) = (backjump_twl_i assignment conf up_map dl) in 
     let bj_assigned_map = reconstruct_assigned_map xs in 
     let (bj_map, _, _) = update_watch_lists_i xs bj_assigned_map f_map l in
      let cdl = (get_current_decision_level xs) in
       let cp = get_checkpoint checkpoints cdl in 
        let b_state = Simplex_inc.backtrack_simplex cp state in
         let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
            (
             match (length bj_u_core) with
                | 0 -> (
                        match (bj_clause, find_conflict_i_map xs bj_assigned_map formula) with 
                            | (Disjunction ([]), _) -> failwith "[Invalid argument] backjump_cdcl: backjump clause empty"
                            | (Disjunction ([y]), []) -> (formula, xs, bj_assigned_map, bj_map, cdl, bj_up_map, bj_state, false)
                            | (Disjunction (ys), []) -> ((learn formula bj_clause), xs, bj_assigned_map, bj_map, cdl, bj_up_map, bj_state, false)
                            | (_, cf) -> if cdl < 1 
                                         then (formula, Assignment ([]), bj_assigned_map, bj_map, cdl, bj_up_map, bj_state, false)
                                         else backjump_cdcl (learn formula bj_clause) xs bj_map bj_up_map checkpoints cdl (hd cf) i_map inv_map bj_state 
                       )
                | _ -> if cdl < 1
                       then (formula, Assignment ([]), bj_assigned_map, bj_map, cdl, bj_up_map, bj_state, false)
                       else (
                             match (bj_clause, find_conflict_i_map xs bj_assigned_map formula) with
                                | (_, []) -> ((learn (learn formula bj_clause) (clauselist_to_neg_clause (convert_unsat_core_i bj_u_core i_map inv_map))), xs, bj_assigned_map, bj_map, cdl, bj_up_map, bj_state, true)
                                | (_, cf) -> backjump_cdcl (learn (learn formula bj_clause) (clauselist_to_neg_clause (convert_unsat_core_i bj_u_core i_map inv_map))) xs bj_map bj_up_map checkpoints cdl (hd cf) i_map inv_map bj_state 
                            )
            );;

let rec dpll_twl_inc_i_rec assignment assigned_map formula f_map up_map s_state checkpoints i_map inv_map dl conf_count r_threshold =
    (*Printing.print_assignment assignment; printf "\n\n";*) (*match model_found_twl_i assignment formula with
        | true -> (
                    (*Printing.print_simplex_constraints sf_assignment;*) 
                   match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) s_state with
                    | Simplex_inc.Inl (unsat_core) -> if dl < 1
                                                      then (false)
                                                      else let (num, cp) = hd (checkpoints) in
                                                            let r_state = Simplex_inc.backtrack_simplex cp s_state in
                                                            (*let ys = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                (*printf "RESTART_MODEL\n\n";*)
                                                                restart_twl_inc_i assignment (learn formula ys) (add_clause_to_map f_map ys) r_state [hd (checkpoints)] i_map inv_map*)
                                                                (
                                                                 match length unsat_core with 
                                                                    | 0 -> failwith "[Invalid argument] unsat core empty"
                                                                    | 1 -> (
                                                                            (*printf "RESTART_UNIT\n\n";*) match (hd (convert_unsat_core_i unsat_core i_map inv_map)) with
                                                                                | Atom (y) -> restart_twl_inc_i_unit assignment formula f_map r_state [hd (checkpoints)] i_map inv_map y false
                                                                                | Not (Atom (y)) -> restart_twl_inc_i_unit assignment formula f_map r_state [hd (checkpoints)] i_map inv_map y true
                                                                                | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: unsat_core does not consist of literals"
                                                                            )
                                                                    | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                             if conf_count > 75
                                                                             then (restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map)
                                                                            else (
                                                                             (*
                                                                             match t_backjump formula (rev (minimal_assignment_for_unsat_core assignment (Disjunction (u_core)))) 1 with
                                                                              | (ys, _, false) -> restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map
                                                                              | (ys, l, true) ->*) let (ys, l, bj_clause) = (backjump_twl_i assignment (learn formula (Disjunction (u_core))) (hd u_core)) in 
                                                                                                    let (bj_map, _, _) = update_watch_lists_i ys f_map l in
                                                                                                  let cdl = (get_current_decision_level ys) in
                                                                                                    let cp = get_checkpoint checkpoints cdl in 
                                                                                                     let b_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                                                      let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
                                                                                                       (
                                                                                                        match (length bj_u_core) with
                                                                                                            | 0 -> (
                                                                                                                    (*printf "BACKJUMP\n\n";*) match (bj_clause, (conflict_exists_i ys (learn formula (Disjunction (u_core))))) with
                                                                                                                        | (_, true) -> restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map
                                                                                                                        | (Disjunction ([]), false) -> dpll_twl_inc_i_rec ys formula bj_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                        | (Disjunction ([v]), false) -> dpll_twl_inc_i_rec ys formula bj_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                        | (Disjunction (vs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_inc_i_rec ys formula_l (add_clause_to_map bj_map (Disjunction (u_core))) bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                                                )
                                                                                                            | _ -> (
                                                                                                                    (*printf "bj_cons\n\n";*) match backjump_to_t_consistent_state ys checkpoints i_map inv_map cdl b_state with 
                                                                                                                    | ([], _, _, _, _) -> restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map
                                                                                                                    | (cons_assignment, cons_cps, cons_state, cons_dl, cons_l) -> let (cons_map, _, _) = update_watch_lists_i (Assignment (cons_assignment)) f_map cons_l in
                                                                                                                                                                        dpll_twl_inc_i_rec (Assignment (cons_assignment)) (learn formula (Disjunction (u_core))) cons_map cons_state cons_cps i_map inv_map cons_dl (conf_count + 1)
                                                                                                                )

                                                                                                        )
                                                                            )
                                                                )
                                                                                          
                    | Simplex_inc.Inr (n_state) -> (* According to my understanding this is sufficient info to determine that formula is SAT *)
                                                    (*Printing.print_assignment assignment; printf "\n\n";*)
                                                    (*let (c, _, _, _) = (Tseitin.Inv_Map.find 26 inv_map) in
                                                    printf "%s\n\n" (Printing.print_constraint_n c);*)
                                                    true
                  )
        | false ->*) 
            let new_cps = checkpoints @ [(dl, Simplex_inc.checkpoint_simplex s_state)] in
                    (*let (new_assignment, new_map, new_dl, new_state, prop, conf) = *)
                match decision_twl_inc_i_map formula assignment assigned_map f_map up_map s_state i_map inv_map dl conf_count with
                     (* This match means there was no literal to use for decision, hence dpll found a potential model *)
                    | (_, _, _, _, _, _, _, _, true) -> (
                            (*Printing.print_simplex_constraints sf_assignment;*) 
                        match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) s_state with
                            | Simplex_inc.Inl (unsat_core) -> if dl < 1
                                                            then ((*printf "test1\n";*) false)
                                                            else let (num, cp) = hd (checkpoints) in
                                                                    let r_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                    (*let ys = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                        (*printf "RESTART_MODEL\n\n";*)
                                                                        restart_twl_inc_i assignment (learn formula ys) (add_clause_to_map f_map ys) r_state [hd (checkpoints)] i_map inv_map*)
                                                                        (
                                                                        match length unsat_core with 
                                                                            | 0 -> failwith "[Invalid argument] unsat core empty"
                                                                            | 1 -> (
                                                                                    (*printf "RESTART_UNIT\n\n";*) match (hd (convert_unsat_core_i unsat_core i_map inv_map)) with
                                                                                        | Atom (y) -> restart_twl_inc_i_unit assignment formula f_map up_map r_state [hd (checkpoints)] i_map inv_map r_threshold y false
                                                                                        | Not (Atom (y)) -> restart_twl_inc_i_unit assignment formula f_map up_map r_state [hd (checkpoints)] i_map inv_map r_threshold y true
                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: unsat_core does not consist of literals"
                                                                                    )
                                                                            | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                                    if conf_count > -1
                                                                                    then (restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) up_map r_state [hd (checkpoints)] i_map inv_map r_threshold)
                                                                                    else (
                                                                                    (*
                                                                                    match t_backjump formula (rev (minimal_assignment_for_unsat_core assignment (Disjunction (u_core)))) 1 with
                                                                                    | (ys, _, false) -> restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map
                                                                                    | (ys, l, true) ->*) let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i assignment (Disjunction (u_core)) up_map dl) in 
                                                                                                          let new_assigned_map = reconstruct_assigned_map ys in
                                                                                                          let (bj_map, _, _) = update_watch_lists_i ys new_assigned_map f_map l in
                                                                                                           let cdl = (get_current_decision_level ys) in
                                                                                                            let cp = get_checkpoint checkpoints cdl in 
                                                                                                            let b_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                                                            let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
                                                                                                            (
                                                                                                                match (length bj_u_core) with
                                                                                                                    | 0 -> (
                                                                                                                            (*printf "BACKJUMP\n\n";*) match (bj_clause, (conflict_exists_i_map ys new_assigned_map (learn formula (Disjunction (u_core))))) with
                                                                                                                                | (_, true) -> (
                                                                                                                                                match backjump_to_conflictless_state formula ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                                                                                    | ([], _, _, _, _, _) -> false 
                                                                                                                                                    | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                                                                        let bj_cons_assigned_map = reconstruct_assigned_map (Assignment (bj_cons_assignment)) in
                                                                                                                                                        let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) bj_cons_assigned_map f_map bj_cons_l in 
                                                                                                                                                            dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) bj_cons_assigned_map (learn formula (Disjunction (u_core))) (add_clause_to_map bj_cons_map (Disjunction (u_core))) bj_cons_up_map bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1) r_threshold
                                                                                                                                               )
                                                                                                                                               (*printf "restart\n"; restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) (decay_and_update_vsids vsids (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map *)
                                                                                                                                | (Disjunction ([]), false) -> dpll_twl_inc_i_rec ys new_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                                                                | (Disjunction ([v]), false) -> dpll_twl_inc_i_rec ys new_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                                                                | (Disjunction (vs), false) -> dpll_twl_inc_i_rec ys new_assigned_map formula (add_clause_to_map bj_map (Disjunction (u_core))) bj_up_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                                                                | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                                                        )
                                                                                                                    | _ -> (
                                                                                                                            (*printf "bj_cons\n\n";*) match backjump_to_t_consistent_state ys bj_up_map checkpoints i_map inv_map cdl b_state with 
                                                                                                                            | ([], _, _, _, _, _) -> false (*restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) (decay_and_update_vsids vsids (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map*)
                                                                                                                            | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) -> 
                                                                                                                                let cons_assigned_map = reconstruct_assigned_map (Assignment (cons_assignment)) in
                                                                                                                                let (cons_map, _, _) = update_watch_lists_i (Assignment (cons_assignment)) cons_assigned_map f_map cons_l in
                                                                                                                                                                                        dpll_twl_inc_i_rec (Assignment (cons_assignment)) cons_assigned_map (learn formula (Disjunction (u_core))) cons_map cons_up_map cons_state cons_cps i_map inv_map cons_dl (conf_count + 1) r_threshold
                                                                                                                        )

                                                                                                                )
                                                                                    )
                                                                        )
                                                                                                
                            | Simplex_inc.Inr (n_state) -> (* According to my understanding this is sufficient info to determine that formula is SAT *)
                                                            (* printf "model_found %s\n\n" (string_of_bool (model_found_twl_i assignment formula));
                                                            Printing.print_assignment assignment; printf "\n\n"; *)
                                                            (*let (c, _, _, _) = (Tseitin.Inv_Map.find 26 inv_map) in
                                                            printf "%s\n\n" (Printing.print_constraint_n c);*)
                                                            true
                        )
                | (new_assignment, new_assigned_map, new_map, new_dl, new_up_map, new_state, prop, conf, false) ->
                    (
                     (*printf "D: "; Printing.print_assignment new_assignment; printf "\n\n";*)
                     match conf with 
                        | [] -> (
                                 match prop with
                                    | [] -> dpll_twl_inc_i_rec new_assignment new_assigned_map formula new_map new_up_map new_state new_cps i_map inv_map new_dl (conf_count) r_threshold
                                    | x :: xs -> let (n_assignment, n_assigned_map, n_map, n_up_map, n_state, n_conf) = unit_propagation_twl_inc_i_map new_assignment new_assigned_map new_map new_up_map new_state i_map inv_map prop new_dl in 
                                                    (
                                                     (*printf "UP: "; Printing.print_assignment n_assignment; printf "\n\n";*)
                                                     match n_conf with
                                                      | [] -> (
                                                                match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                    | Inl (unsat_core) -> let (num, cp) = hd (checkpoints) in
                                                                                          let r_state = Simplex_inc.backtrack_simplex cp n_state in
                                                                                          (
                                                                                           match length unsat_core with 
                                                                                            | 0 -> failwith "[Invalid argument] unsat core empty"
                                                                                            | 1 -> (
                                                                                                    (*printf "RESTART_UNIT\n\n";*) match (hd (convert_unsat_core_i unsat_core i_map inv_map)) with
                                                                                                        | Atom (y) -> restart_twl_inc_i_unit new_assignment formula f_map n_up_map r_state [hd (checkpoints)] i_map inv_map r_threshold y false
                                                                                                        | Not (Atom (y)) -> restart_twl_inc_i_unit new_assignment formula f_map n_up_map r_state [hd (checkpoints)] i_map inv_map r_threshold y true
                                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: unsat_core does not consist of literals"
                                                                                                   )
                                                                                            | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                                                    if conf_count > -1
                                                                                                    then (restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map n_map (Disjunction (u_core))) n_up_map r_state [hd (checkpoints)] i_map inv_map) r_threshold
                                                                                                    else ( 
                                                                                                    (*match t_backjump formula (rev (minimal_assignment_for_unsat_core n_assignment (Disjunction (u_core)))) 1 with
                                                                                                    | (ys, _, false) -> restart_twl_inc_i assignment (learn formula (Disjunction (u_core))) (add_clause_to_map n_map (Disjunction (u_core))) r_state [hd (checkpoints)] i_map inv_map
                                                                                                    | (ys, l, true) ->*) let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i n_assignment (Disjunction (u_core)) n_up_map new_dl) in 
                                                                                                                         let bj_assigned_map = reconstruct_assigned_map ys in
                                                                                                                        let (bj_map, _, _) = update_watch_lists_i ys bj_assigned_map f_map l in
                                                                                                                        let cdl = (get_current_decision_level ys) in
                                                                                                                         let cp = get_checkpoint new_cps cdl in 
                                                                                                                          let b_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                                                                            let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
                                                                                                                            (
                                                                                                                                match (length bj_u_core) with
                                                                                                                                    | 0 -> (
                                                                                                                                            (*printf "BACKJUMP\n\n";*) match (bj_clause, (conflict_exists_i_map ys bj_assigned_map (learn formula (Disjunction (u_core))))) with
                                                                                                                                                | (_, true) -> if cdl < 1 
                                                                                                                                                               then false 
                                                                                                                                                               else (
                                                                                                                                                                    match backjump_to_conflictless_state formula ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                                                                                                        | ([], _, _, _, _, _) -> false 
                                                                                                                                                                        | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                                                                                          let bj_cons_assigned_map = reconstruct_assigned_map (Assignment (bj_cons_assignment)) in
                                                                                                                                                                          let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) bj_cons_assigned_map new_map bj_cons_l in 
                                                                                                                                                                            dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) bj_cons_assigned_map (learn formula (Disjunction (u_core))) (add_clause_to_map bj_cons_map (Disjunction (u_core))) bj_cons_up_map bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1) r_threshold
                                                                                                                                                                    )
                                                                                                                                                                    (*restart_twl_inc_i n_assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) (decay_and_update_vsids vsids (Disjunction (u_core))) r_state [hd (new_cps)] i_map inv_map*)
                                                                                                                                                | (Disjunction ([]), false) -> dpll_twl_inc_i_rec ys bj_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                                                                                | (Disjunction ([v]), false) -> dpll_twl_inc_i_rec ys bj_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                                                                                | (Disjunction (vs), false) -> dpll_twl_inc_i_rec ys bj_assigned_map formula (add_clause_to_map bj_map (Disjunction (u_core))) bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                                                                                | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                                                                        )
                                                                                                                                    | _ -> (
                                                                                                                                            (*printf "bj_cons\n\n";*) match backjump_to_t_consistent_state ys bj_up_map new_cps i_map inv_map cdl b_state with 
                                                                                                                                            | ([], _, _, _, _, _) -> false (*restart_twl_inc_i n_assignment (learn formula (Disjunction (u_core))) (add_clause_to_map f_map (Disjunction (u_core))) (decay_and_update_vsids vsids (Disjunction (u_core))) r_state [hd (new_cps)] i_map inv_map*)
                                                                                                                                            | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) -> 
                                                                                                                                                let cons_assigned_map = reconstruct_assigned_map (Assignment (cons_assignment)) in
                                                                                                                                                let (cons_map, _, _) = update_watch_lists_i (Assignment (cons_assignment)) cons_assigned_map f_map cons_l in
                                                                                                                                                dpll_twl_inc_i_rec (Assignment (cons_assignment)) cons_assigned_map (learn formula (Disjunction (u_core))) cons_map cons_up_map cons_state cons_cps i_map inv_map cons_dl (conf_count + 1) r_threshold
                                                                                                                                           )

                                                                                                                                )
                                                                                                    )
                                                                                          )
                                                                    | Inr (state) -> dpll_twl_inc_i_rec n_assignment n_assigned_map formula n_map n_up_map state new_cps i_map inv_map new_dl (conf_count) r_threshold
                                                               )
                                                      | z :: zs -> (*printf "non-empty conf\n\n";
                                                                    printf "n_conf: %s\n\n" (Printing.print_element_list n_conf);*)
                                                                    if conf_count > r_threshold
                                                                    then ( let (num, cp) = hd (checkpoints) in
                                                                            let r_state = Simplex_inc.backtrack_simplex cp n_state in
                                                                             let Disjunction (conf_list) = z in 
                                                                              let ys = (clauselist_to_neg_clause (conf_list)) in 
                                                                                restart_twl_inc_i n_assignment (learn formula ys) (add_clause_to_map n_map ys) n_up_map r_state [hd (checkpoints)] i_map inv_map r_threshold
                                                                        )
                                                                    else
                                                                    ( 
                                                                    let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i n_assignment (hd n_conf) n_up_map new_dl) in 
                                                                     let bj_assigned_map = reconstruct_assigned_map ys in
                                                                     let (bj_map, _, _) = update_watch_lists_i ys bj_assigned_map new_map l in
                                                                     let cdl = (get_current_decision_level ys) in
                                                                     let cp = get_checkpoint new_cps cdl in 
                                                                       let b_state = Simplex_inc.backtrack_simplex cp n_state in
                                                                        let (bj_state, unsat_core) = assert_backjump l i_map inv_map b_state in
                                                                        let (num, cp_0) = hd (new_cps) in
                                                                        let r_state = Simplex_inc.backtrack_simplex cp_0 bj_state in
                                                                         (
                                                                          match (length unsat_core) with
                                                                            | 0 -> (
                                                                                    (*printf "BACKJUMP\n\n";*) match (bj_clause, (find_conflict_i_map ys bj_assigned_map formula)) with
                                                                                        | (Disjunction ([]), []) -> dpll_twl_inc_i_rec ys bj_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                        | (Disjunction ([v]), []) -> dpll_twl_inc_i_rec ys bj_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                        | (Disjunction (vs), []) -> dpll_twl_inc_i_rec ys bj_assigned_map (learn formula bj_clause) (add_clause_to_map bj_map bj_clause) bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                                                        | (Disjunction ([]), cf) -> failwith "[Invalid argument] backjump clause empty\n"; (*if cdl < 1 
                                                                                                                    then false 
                                                                                                                    else (*Printing.print_assignment ys; printf "\n\n";*)
                                                                                                     let Disjunction (cf_ls) = hd cf in (*printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls));*)
                                                                                                     (*(
                                                                                                      match backjump_to_conflictless_state formula ys new_cps cdl bj_state with 
                                                                                                        | ([], _, _, _, _) -> false 
                                                                                                        | (bj_cons_assignment, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                           let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) new_map bj_cons_l in 
                                                                                                            dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) (learn formula (clauselist_to_neg_clause cf_ls)) bj_cons_map (sort compare_vsids (decay_and_update_vsids vsids (clauselist_to_neg_clause cf_ls))) bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                                     )*)
                                                                                                     restart_twl_inc_i ys (learn formula (Disjunction (cf_ls))) (add_clause_to_map bj_map (Disjunction (cf_ls))) (decay_and_update_vsids vsids (Disjunction (cf_ls))) r_state [hd (new_cps)] i_map inv_map*)
                                                                                        (*| (Disjunction ([v]), cf) -> if cdl < 1 
                                                                                                                     then ((*printf "test2\n";*) false )
                                                                                                                     else 
                                                                                                                        (* Printing.print_assignment ys; printf "\n\n";*)
                                                                                                                        (*let Disjunction (cf_ls) = hd cf in (*) printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls));*)
                                                                                                                        (
                                                                                                                        match backjump_to_conflictless_state formula ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                                                            | ([], _, _, _, _, _) -> (*printf "test3\n";*) false 
                                                                                                                            | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                                            let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) new_map bj_cons_l in 
                                                                                                                                dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) formula bj_cons_map bj_cons_up_map (sort compare_vsids (decay_and_update_vsids vsids (hd cf))) bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                                                        )*)*)
                                                                                                     (*restart_twl_inc_i ys (learn formula (Disjunction (cf_ls))) (add_clause_to_map bj_map (Disjunction (cf_ls))) (decay_and_update_vsids vsids (Disjunction (cf_ls))) r_state [hd (new_cps)] i_map inv_map*)
                                                                                        | (Disjunction (vs), cf) -> if cdl < 1 
                                                                                                                    then ((*printf "test4\n";*) false )
                                                                                                                    else (
                                                                                                                          match (backjump_cdcl formula ys bj_map bj_up_map new_cps cdl (hd cf) i_map inv_map bj_state) with 
                                                                                                                            | (_, Assignment ([]), _, _, _, _, _, _) -> (*printf "test1\n";*) false 
                                                                                                                            | (formula_cdcl, assignment_cdcl, assigned_map_cdcl, map_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, true) -> 
                                                                                                                                 (* TODO: maybe think about updating vsids in the backjump_cdcl function as well *)
                                                                                                                                restart_twl_inc_i assignment_cdcl formula_cdcl map_cdcl up_map_cdcl r_state [hd (checkpoints)] i_map inv_map r_threshold
                                                                                                                            | (formula_cdcl, assignment_cdcl, assigned_map_cdcl, map_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, false) ->
                                                                                                                                dpll_twl_inc_i_rec assignment_cdcl assigned_map_cdcl formula_cdcl map_cdcl up_map_cdcl state_cdcl (reset_checkpoints new_cps cdl) i_map inv_map dl_cdcl (conf_count + 1) r_threshold
                                                                                                                         )
                                                                                                                        (*( (*(Printing.print_assignment ys; printf "\n\n";*)
                                                                                                                        let Disjunction (cf_ls) = hd cf in (*printf "cf: %s\n\n" (Printing.print_element (hd cf));*)
                                                                                                                        (
                                                                                                                        match backjump_to_conflictless_state (learn formula bj_clause) ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                                                            | ([], _, _, _, _, _) -> (*printf "test5\n";*) false 
                                                                                                                            | (bj_cons_assignment, bj_cons_up_map,  bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                                            let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) new_map bj_cons_l in 
                                                                                                                                dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) formula bj_cons_map bj_cons_up_map (sort compare_vsids (decay_and_update_vsids vsids (hd cf))) bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                                                        ))*)
                                                                                                     (*restart_twl_inc_i ys (learn (learn formula (Disjunction (cf_ls))) bj_clause) (add_clause_to_map (add_clause_to_map bj_map (Disjunction (cf_ls))) bj_clause) (decay_and_update_vsids vsids bj_clause) r_state [hd (new_cps)] i_map inv_map)*)
                                                                                                     (*if cdl < 1
                                                                                                     then (Printing.print_assignment ys; printf "\n\n%s\n" (Printing.print_element (hd (cf))); false)
                                                                                                     else let Disjunction (cf_ls) = hd cf in 
                                                                                                     (printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls)); restart_twl_inc_i new_assignment (learn formula (clauselist_to_neg_clause cf_ls)) (add_clause_to_map new_map (clauselist_to_neg_clause cf_ls)) (decay_and_update_vsids vsids (bj_clause)) r_state [hd (new_cps)] i_map inv_map)*)
                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                   )
                                                                            | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in
                                                                                   restart_twl_inc_i assignment (learn (learn formula bj_clause) (Disjunction (u_core))) (add_clause_to_map (add_clause_to_map bj_map bj_clause) (Disjunction (u_core))) bj_up_map r_state [hd (checkpoints)] i_map inv_map r_threshold
                                                                                   (*
                                                                                    (*printf "bj_cons\n\n";*) match backjump_to_t_consistent_state ys bj_up_map new_cps i_map inv_map cdl b_state with 
                                                                                     | ([], _, _, _, _, _) -> (*printf "test6\n";*) false
                                                                                     | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) -> let (cons_map, _, _) = update_watch_lists_i (Assignment (cons_assignment)) new_map cons_l in
                                                                                                                                        (* TODO: add unsat_core to cons_map before the recursive call *)
                                                                                                                                                dpll_twl_inc_i_rec (Assignment (cons_assignment)) (learn formula (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map))) cons_map cons_up_map (sort compare_vsids (decay_and_update_vsids vsids (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)))) cons_state cons_cps i_map inv_map cons_dl (conf_count + 1)
                                                                                   *)

                                                                         )
                                                                   )
                                                    )
                                )
                        | x :: xs -> (*printf "non-empty conf\n\n";
                                     printf "conf: %s\n\n" (Printing.print_element_list conf);*)
                                    if conf_count > r_threshold
                                    then ( let Disjunction (conf_list) = x in let ys = (clauselist_to_neg_clause (conf_list)) in 
                                            let (num, cp) = hd (checkpoints) in
                                             let r_state = Simplex_inc.backtrack_simplex cp s_state in 
                                              restart_twl_inc_i new_assignment (learn formula ys) (add_clause_to_map new_map ys) new_up_map r_state [hd (checkpoints)] i_map inv_map r_threshold)
                                    else
                                     (
                                     let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i new_assignment (hd conf) new_up_map new_dl) in 
                                     let bj_assigned_map = reconstruct_assigned_map ys in 
                                     let (bj_map, _, _) = update_watch_lists_i ys bj_assigned_map new_map l in
                                       let cdl = (get_current_decision_level ys) in
                                       let cp = get_checkpoint new_cps cdl in 
                                         let b_state = Simplex_inc.backtrack_simplex cp new_state in 
                                          let (bj_state, unsat_core) = assert_backjump l i_map inv_map b_state in
                                          let (num, cp_0) = hd (new_cps) in
                                          let r_state = Simplex_inc.backtrack_simplex cp_0 bj_state in
                                            (
                                             match (length unsat_core) with
                                                | 0 -> (
                                                        (*printf "BACKJUMP\n\n";*) match (bj_clause, (find_conflict_i_map ys bj_assigned_map formula)) with
                                                        | (Disjunction ([]), []) -> dpll_twl_inc_i_rec ys bj_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                        | (Disjunction ([v]), []) -> dpll_twl_inc_i_rec ys bj_assigned_map formula bj_map bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                        | (Disjunction (vs), []) -> dpll_twl_inc_i_rec ys bj_assigned_map (learn formula bj_clause) (add_clause_to_map bj_map bj_clause) bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1) r_threshold
                                                        | (Disjunction ([]), cf) -> failwith "[Invalid argument] backjump clause empty\n"; (*if cdl < 1 
                                                                                    then false 
                                                                                    else (*Printing.print_assignment ys; printf "\n\n";*)
                                                                    let Disjunction (cf_ls) = hd cf in (*printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls));*)
                                                                    (*(
                                                                      match backjump_to_conflictless_state formula ys new_cps cdl bj_state with 
                                                                        | ([], _, _, _, _) -> false 
                                                                        | (bj_cons_assignment, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                          let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) new_map bj_cons_l in 
                                                                            dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) (learn formula (clauselist_to_neg_clause cf_ls)) bj_cons_map (sort compare_vsids (decay_and_update_vsids vsids (clauselist_to_neg_clause cf_ls))) bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                     )*)
                                                                     restart_twl_inc_i ys (learn formula (Disjunction (cf_ls))) (add_clause_to_map bj_map (Disjunction (cf_ls))) (decay_and_update_vsids vsids (Disjunction (cf_ls))) r_state [hd (new_cps)] i_map inv_map*)
                                                        (*| (Disjunction ([v]), cf) -> if cdl < 1 
                                                                                    then ((*printf "test7\n";*) false) 
                                                                                    else (*Printing.print_assignment ys; printf "\n\n";*)
                                                                                        let Disjunction (cf_ls) = hd cf in (*printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls));*)
                                                                                        (
                                                                                        match backjump_to_conflictless_state formula ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                            | ([], _, _, _, _, _) -> (*printf "test8\n";*) false 
                                                                                            | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                            let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) new_map bj_cons_l in 
                                                                                                dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) formula bj_cons_map bj_cons_up_map (sort compare_vsids (decay_and_update_vsids vsids (hd cf))) bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                        ) *)
                                                                     (*restart_twl_inc_i ys (learn formula (Disjunction (cf_ls))) (add_clause_to_map bj_map (Disjunction (cf_ls))) (decay_and_update_vsids vsids (Disjunction (cf_ls))) r_state [hd (new_cps)] i_map inv_map*)
                                                        | (Disjunction (vs), cf) -> if cdl < 1 
                                                                                    then ((*printf "test3\n";*) false)
                                                                                    else ( 
                                                                                          match (backjump_cdcl formula ys bj_map bj_up_map new_cps cdl (hd cf) i_map inv_map bj_state) with 
                                                                                            | (_, Assignment ([]), _, _, _, _, _, _) -> false 
                                                                                            | (formula_cdcl, assignment_cdcl, assigned_map_cdcl, map_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, true) -> 
                                                                                                (* TODO: maybe think about updating vsids in the backjump_cdcl function as well *)
                                                                                                restart_twl_inc_i assignment_cdcl formula_cdcl map_cdcl up_map_cdcl r_state [hd (checkpoints)] i_map inv_map r_threshold
                                                                                            | (formula_cdcl, assignment_cdcl, assigned_map_cdcl, map_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, false) ->
                                                                                                dpll_twl_inc_i_rec assignment_cdcl assigned_map_cdcl formula_cdcl map_cdcl up_map_cdcl state_cdcl (reset_checkpoints new_cps cdl) i_map inv_map dl_cdcl (conf_count + 1) r_threshold
                                                                                         )
                                                                                  (*if cdl < 1 
                                                                                    then ((*printf "test9\n";*) false) 
                                                                                    else (*Printing.print_assignment ys; printf "\n\n";*)
                                                                                        let Disjunction (cf_ls) = hd cf in (*printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls)); *)
                                                                                        ( 
                                                                                        match backjump_to_conflictless_state (learn formula bj_clause) ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                            | ([], _, _, _, _, _) -> (*printf "test10\n";*) (*printf "BEFORE BJ:\n\n"; Printing.print_assignment new_assignment; printf "\n\nconflict: %s" (Printing.print_element (hd conf)); printf "\n\nAFTER_BJ:\n\n"; Printing.print_assignment ys; printf "\ncf: %s\n\n" (Printing.print_element (hd cf)); Printing.print_formula formula;*) false 
                                                                                            | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                            let (bj_cons_map, _, _) = update_watch_lists_i (Assignment (bj_cons_assignment)) new_map bj_cons_l in 
                                                                                                dpll_twl_inc_i_rec (Assignment (bj_cons_assignment)) formula bj_cons_map bj_cons_up_map (sort compare_vsids (decay_and_update_vsids vsids (hd cf))) bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                        )*)
                                                                     (*restart_twl_inc_i ys (learn (learn formula (Disjunction (cf_ls))) bj_clause) (add_clause_to_map (add_clause_to_map bj_map (Disjunction (cf_ls))) bj_clause) (decay_and_update_vsids vsids bj_clause) r_state [hd (new_cps)] i_map inv_map*)
                                                                    (*if cdl < 1
                                                                     then (printf "3 "; false) 
                                                                     else let Disjunction (cf_ls) = hd cf in
                                                                     printf "cf: %s\n\n" (Printing.print_element (clauselist_to_neg_clause cf_ls)); restart_twl_inc_i assignment (learn formula (clauselist_to_neg_clause cf_ls)) (add_clause_to_map f_map (clauselist_to_neg_clause cf_ls)) (decay_and_update_vsids vsids bj_clause) r_state [hd (new_cps)] i_map inv_map*)
                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                        )
                                                | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in
                                                            restart_twl_inc_i assignment (learn (learn formula bj_clause) (Disjunction (u_core))) (add_clause_to_map (add_clause_to_map bj_map bj_clause) (Disjunction (u_core))) bj_up_map r_state [hd (checkpoints)] i_map inv_map r_threshold
                                                      (*
                                                        (*printf "bj_cons\n\n";*) match backjump_to_t_consistent_state ys bj_up_map new_cps i_map inv_map cdl b_state with 
                                                        | ([], _, _, _, _, _) -> (*printf "test11\n";*) false 
                                                                              (*let u_core = (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)) in 
                                                                             restart_twl_inc_i new_assignment (learn formula u_core) (add_clause_to_map f_map u_core) (decay_and_update_vsids vsids u_core) r_state [hd (new_cps)] i_map inv_map*)
                                                        | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) -> let (cons_map, _, _) = update_watch_lists_i (Assignment (cons_assignment)) new_map cons_l in
                                                                                                                    dpll_twl_inc_i_rec (Assignment (cons_assignment)) (learn formula (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map))) cons_map cons_up_map (sort compare_vsids (decay_and_update_vsids vsids (clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)))) cons_state cons_cps i_map inv_map cons_dl (conf_count + 1)
                                                      *)
                                            )
                                     )         
                    
                    )

and dpll_twl_inc_i formula up_map i_map inv_map s_state checkpoints = 
                let (new_formula, new_assignment, new_up_map, prop, conf_unit, new_state, to_update) = preprocess_unit_clauses_inc_i (Assignment ([])) formula up_map s_state i_map inv_map in 
                        (*Printing.print_formula new_formula; printf "\n\n"; *)
                        if conf_unit 
                        then false
                        else (
                              let (f_map, literals) = construct_map new_formula in 
                               let new_assigned_map = reconstruct_assigned_map new_assignment in
                                let (f_map_new, prop_new, conf_new) = update_watch_lists_i_l new_assignment new_assigned_map f_map to_update in
                                    let (n_assignment, n_assigned_map, n_map, n_up_map, n_state, conf) = unit_propagation_twl_inc_i_map new_assignment new_assigned_map f_map_new new_up_map new_state i_map inv_map prop 0 in 
                                        (
                                        match conf with
                                            | [] -> dpll_twl_inc_i_rec n_assignment n_assigned_map new_formula n_map n_up_map n_state checkpoints i_map inv_map 0 0 10
                                            | x :: xs -> false
                                        )
                            )

and restart_twl_inc_i assignment formula f_map up_map s_state checkpoints i_map inv_map r_threshold = 
                        (*Printing.print_assignment assignment; printf "\n\n";*) (*printf "RESTART\n";*)  let (new_formula, new_assignment, new_up_map, prop, conf_unit, new_state, to_update) = preprocess_unit_clauses_inc_i (preserve_unit_assignments assignment) formula up_map s_state i_map inv_map in 
                            if conf_unit
                            then (false)
                            else (let (ra_state, ra_conf, ra_to_update) = reassert_after_restart new_assignment i_map inv_map new_state in
                                    (*printf "POST_REASSERT\n\n";*) (
                                     if length ra_conf > 0
                                     then (false)
                                     else (
                                           let new_assigned_map = reconstruct_assigned_map new_assignment in
                                           let (f_map_new, prop_new, conf_new) = update_watch_lists_i_l new_assignment new_assigned_map f_map (to_update @ ra_to_update) in
                                           (*printf "to_update: %s\n\n" (Printing.print_element_list (to_update @ ra_to_update));
                                           printf "prop_new: %s\n\n" (Printing.print_element_list prop_new);*)
                                            let (n_assignment, n_assigned_map, n_map, n_up_map, n_state, conf) = unit_propagation_twl_inc_i_map new_assignment new_assigned_map f_map_new new_up_map ra_state i_map inv_map prop_new 0 in 
                                                (
                                                match conf with
                                                    | [] -> (*Printing.print_formula new_formula; printf "\n\n";*)
                                                            (*Printing.print_assignment n_assignment; printf "\n\n";*)
                                                        dpll_twl_inc_i_rec n_assignment n_assigned_map new_formula n_map n_up_map n_state checkpoints i_map inv_map 0 0 (r_threshold + 10)
                                                    | x :: xs -> (*Printing.print_formula new_formula; printf "\n\n"; *)
                                                                (*Printing.print_assignment n_assignment; printf "\n\n";
                                                                printf "conf: %s\n\n" (Printing.print_element_list conf);*)
                                                                (*printf "test14\n";*)
                                                                false
                                                )
                                          )
                                    )
                                 )
                                                
and restart_twl_inc_i_unit assignment formula f_map up_map s_state checkpoints i_map inv_map r_threshold unit_literal lit_val = 
                        (*printf "RESTART_UNIT\n";*) let (new_formula, new_assignment, new_up_map, prop, conf_unit, new_state, to_update) = preprocess_unit_clauses_inc_i (preserve_unit_assignments assignment) formula up_map s_state i_map inv_map in
                            (*Printing.print_assignment new_assignment; printf "\n\n";*) if conf_unit
                            then false
                            else (
                                  let (ra_state, ra_conf, ra_to_update) = reassert_after_restart new_assignment i_map inv_map new_state in
                                    (*printf "POST_REASSERT\n\n";*) (
                                     if length ra_conf > 0
                                     then (false)
                                     else (
                                           let new_assigned_map = reconstruct_assigned_map new_assignment in
                                           let (f_map_new, prop_new, conf_new) = update_watch_lists_i_l new_assignment new_assigned_map f_map (ra_to_update @ to_update) in
                                              let Assignment (xs) = new_assignment in
                                              if (is_assigned_i_map new_assignment new_assigned_map (Atom (unit_literal)))
                                              then false
                                              else (
                                                    let (n_assignment, n_assigned_map, n_map, n_up_map, n_state, conf) = unit_propagation_twl_inc_i_map (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) new_assigned_map f_map new_up_map ra_state i_map inv_map prop_new 0 in
                                                    (
                                                    match conf with
                                                        | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) 
                                                                dpll_twl_inc_i_rec n_assignment n_assigned_map new_formula n_map n_up_map n_state checkpoints i_map inv_map 0 0 (r_threshold + 1)
                                                        | x :: xs -> false
                                                    )
                                                  )
                                          )
                                    )
                                 );;

(**********************************************************************************************************************)

let rec update_modifiable_clause_rec clause literal acc =
    match clause with
        | ([], cls) -> (
                        match (length acc) with
                            | 0 -> ([], [(Disjunction (cls), Disjunction (cls))], true)
                            | 1 -> ([(acc, cls)], [(hd acc, Disjunction (cls))], false)
                            | _ -> ([(acc, cls)], [], false)
                       )
        | (x :: xs, cls) -> (
                                            match (x, literal) with 
                                                | (Atom (l), Atom (r)) -> if compare l r = 0 
                                                                        then ([], [], false)
                                                                        else update_modifiable_clause_rec (xs, cls) literal (acc @ [x])
                                                | (Not (Atom (l)), Atom (r)) -> if compare l r = 0
                                                                                then update_modifiable_clause_rec (xs, cls) literal acc
                                                                                else update_modifiable_clause_rec (xs, cls) literal (acc @ [x])
                                                | (Atom (l), Not (Atom (r))) -> if compare l r = 0
                                                                                then update_modifiable_clause_rec (xs, cls) literal acc
                                                                                else update_modifiable_clause_rec (xs, cls) literal (acc @ [x])
                                                | (Not (Atom (l)), Not (Atom (r))) -> if compare l r = 0
                                                                                    then ([], [], false)
                                                                                    else update_modifiable_clause_rec (xs, cls) literal (acc @ [x])
                                            );;

let update_modifiable_clause clause literal = update_modifiable_clause_rec clause literal [];;

let rec update_modifiable_formula_rec f f_mod literal acc prop = 
    match f_mod with 
        | [] -> (acc, prop, [])
        | x :: xs -> (
                      match update_modifiable_clause x literal with
                        | ([], [], false) -> update_modifiable_formula_rec f xs literal acc prop
                        | (y, [], false) -> update_modifiable_formula_rec f xs literal (acc @ y) prop
                        | (y, p, false) -> update_modifiable_formula_rec f xs literal (acc @ y) (prop @ p)
                        | (_, conf, true) -> let (_, cf) = hd conf in (f, [], [cf])
                     );;

let update_modifiable_formula f_mod literal = update_modifiable_formula_rec f_mod f_mod literal [] [];;

let rec reconstruct_modifiable_formula_rec formula assignment = 
    match assignment with 
        | Assignment ([]) -> (formula, [])
        | Assignment ((c, v, d, dl) :: xs) -> if v
                                              then (
                                                    match update_modifiable_formula formula (Atom (c)) with
                                                    | (ys, _, []) -> reconstruct_modifiable_formula_rec ys (Assignment (xs))
                                                    | (ys, _, conf) -> (ys, conf)
                                                   )
                                              else (
                                                    match update_modifiable_formula formula (Not (Atom (c))) with
                                                    | (ys, _, []) -> reconstruct_modifiable_formula_rec ys (Assignment (xs))
                                                    | (ys, _, conf) -> (ys, conf)
                                                   );;

let reconstruct_modifiable_formula formula assignment = reconstruct_modifiable_formula_rec (Util.construct_modifiable_formula formula) assignment;;

let choose_decision_literal_list clause = 
    match clause with
     | ([], _) -> failwith "[Invalid argument] choose_decision_literal_list: clause empty"
     | (x :: xs, _) -> x;;

let rec decision_inc_i_list assignment f_mod up_map s_state i_map inv_map dl conf_count =
    match f_mod with
     | [] -> (assignment, f_mod, dl, up_map, s_state, [], [], true)
     | c :: cs -> ( let Assignment (xs) = assignment in
                     match (choose_decision_literal_list c) with 
                        | Atom (x) -> if is_proper_constraint x
                                      then (
                                            match x with 
                                                | Constraint (y) -> (
                                                                     match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map))) s_state with
                                                                        | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), f_mod, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                        | Inr (n_state) -> let (new_f_mod, prop, conf) = update_modifiable_formula f_mod (Atom (x)) in 
                                                                                                (Assignment (xs @ [(x, true, true, dl + 1)]), new_f_mod, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                    )   
                                                | Index (y) -> (
                                                                let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in
                                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int y)) s_state with
                                                                    | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), f_mod, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                    | Inr (n_state) -> let (new_f_mod, prop, conf) = update_modifiable_formula f_mod (Atom (x)) in 
                                                                                            (Assignment (xs @ [(x, true, true, dl + 1)]), new_f_mod, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), n_state, prop, conf, false)
                                                                )   
                                            )
                                      else (  
                                            let (new_f_mod, prop, conf) = update_modifiable_formula f_mod (Atom (x)) in
                                                (Assignment (xs @ [(x, true, true, dl + 1)]), new_f_mod, dl + 1, (UP_Map.add (Printing.print_element (Atom (x))) (Disjunction ([])) up_map), s_state, prop, conf, false)
                                           )
                        | Not (Atom (x)) ->
                                            if is_proper_constraint x
                                            then (
                                                  match x with
                                                    | Constraint (y) -> (
                                                                         match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n x) i_map))) s_state with
                                                                            | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), f_mod, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                            | Inr (n_state) -> let (new_f_mod, prop, conf) = update_modifiable_formula f_mod (Not (Atom (x))) in 
                                                                                                    (Assignment (xs @ [(x, false, true, dl + 1)]), new_f_mod, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                        )
                                                    | Index (y) -> (
                                                                    let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find y inv_map) in 
                                                                     match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map))) s_state with
                                                                        | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), f_mod, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, [], [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)], false)
                                                                        | Inr (n_state) -> let (new_f_mod, prop, conf) = update_modifiable_formula f_mod (Not (Atom (x))) in 
                                                                                            (Assignment (xs @ [(x, false, true, dl + 1)]), new_f_mod, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), n_state, prop, conf, false) 
                                                                   )
                                                 )
                                            else (
                                                  let (new_f_mod, prop, conf) = update_modifiable_formula f_mod (Not (Atom (x))) in
                                                    (Assignment (xs @ [(x, false, true, dl + 1)]), new_f_mod, dl + 1, (UP_Map.add (Printing.print_element (Not (Atom (x)))) (Disjunction ([])) up_map), s_state, prop, conf, false) 
                                                 )
                        | _ -> failwith "[Invalid argument] decision_twl_inc: choose_decision_literal_list did not return a literal"
                  )
     | _ -> failwith "[Invalid argument] decision_twl_inc: formula not in CNF";;

let rec unit_propagation_inc_i_list assignment f_mod up_map s_state i_map inv_map prop dl = 
    match prop with 
        | [] -> (assignment, f_mod, up_map, s_state, [])
        | up_pair :: xs -> (
                      let Assignment (ys) = assignment in 
                      let (x, clause) = up_pair in
                       match x with
                        | Atom (y) -> if is_proper_constraint y 
                                      then (
                                            match y with 
                                                | Constraint (z) -> (
                                                                     match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map))) s_state with
                                                                        | Inl (unsat_core) -> (Assignment (ys @ [(y, true, false, dl)]), f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                        | Inr (n_state) -> let (new_f_mod, new_prop, conf) = update_modifiable_formula f_mod (Atom (y)) in 
                                                                                            (
                                                                                            match conf with 
                                                                                                | [] -> unit_propagation_inc_i_list (Assignment (ys @ [(y, true, false, dl)])) new_f_mod (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                            )
                                                                    )
                                                | Index (z) -> (
                                                                let (s, v, d, tmp_dl) = (Tseitin.Inv_Map.find z inv_map) in
                                                                 match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int z)) s_state with
                                                                        | Inl (unsat_core) -> (Assignment (ys @ [(y, true, false, dl)]), f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                        | Inr (n_state) -> let (new_f_mod, new_prop, conf) = update_modifiable_formula f_mod (Atom (y)) in 
                                                                                            (
                                                                                            match conf with 
                                                                                                | [] -> unit_propagation_inc_i_list (Assignment (ys @ [(y, true, false, dl)])) new_f_mod (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                            )
                                                               )
                                            )
                                      else (
                                            let (new_f_mod, new_prop, conf) = update_modifiable_formula f_mod (Atom (y)) in 
                                            (
                                            match conf with 
                                                | [] -> unit_propagation_inc_i_list (Assignment (ys @ [(y, true, false, dl)])) new_f_mod (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl
                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                            )
                                           )
                        | Not (Atom (y)) -> if is_proper_constraint y 
                                                then (
                                                      match y with
                                                        | Constraint (z) -> (
                                                                             match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n y)) i_map))) s_state with
                                                                                | Inl (unsat_core) -> (Assignment (ys @ [(y, false, false, dl)]), f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                                | Inr (n_state) -> let (new_f_mod, new_prop, conf) = update_modifiable_formula f_mod (Not (Atom (y))) in 
                                                                                                    ( 
                                                                                                    match conf with
                                                                                                        | [] -> unit_propagation_inc_i_list (Assignment (ys @ [(y, false, false, dl)])) new_f_mod (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                        | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                                    )
                                                                            )
                                                        | Index (z) -> (
                                                                        let (c, v, d, tmp_dl) = (Tseitin.Inv_Map.find z inv_map) in 
                                                                         match Simplex_inc.assert_simplex Simplex_inc.equal_nat (Simplex_inc.lrv_QDelta, Simplex_inc.equal_QDelta) (Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n c)) i_map))) s_state with
                                                                            | Inl (unsat_core) -> (Assignment (ys @ [(y, false, false, dl)]), f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, [clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map)])
                                                                            | Inr (n_state) -> let (new_f_mod, new_prop, conf) = update_modifiable_formula f_mod (Not (Atom (y))) in 
                                                                                                ( 
                                                                                                 match conf with
                                                                                                    | [] -> unit_propagation_inc_i_list (Assignment (ys @ [(y, false, false, dl)])) new_f_mod (UP_Map.add (Printing.print_element x) clause up_map) n_state i_map inv_map (xs @ new_prop) dl
                                                                                                    | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                                                                )
                                                                       )
                                                     )
                                                else (
                                                      let (new_f_mod, new_prop, conf) = update_modifiable_formula f_mod (Not (Atom (y))) in 
                                                        ( 
                                                        match conf with
                                                            | [] -> unit_propagation_inc_i_list (Assignment (ys @ [(y, false, false, dl)])) new_f_mod (UP_Map.add (Printing.print_element x) clause up_map) s_state i_map inv_map (xs @ new_prop) dl
                                                            | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_f_mod, (UP_Map.add (Printing.print_element x) clause up_map), s_state, conf)
                                                        )
                                                    )
                        | _ -> failwith "[Invalid argument] unit_propagation_twl: list of propagation literals contains a non-literal element"
                     );;

let rec backjump_cdcl_list formula assignment up_map checkpoints dl conf i_map inv_map state = 
    let (xs, l, bj_clause, bj_up_map) = (backjump_twl_i assignment conf up_map dl) in 
     let cdl = (get_current_decision_level xs) in
      let cp = get_checkpoint checkpoints cdl in 
       let b_state = Simplex_inc.backtrack_simplex cp state in
        let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
         let formula_new = learn formula bj_clause in
          let (formula_mod, cf) = reconstruct_modifiable_formula formula_new xs in 
            (
             match (length bj_u_core) with
                | 0 -> (
                        match (bj_clause, cf) with 
                            | (Disjunction ([]), _) -> failwith "[Invalid argument] backjump_cdcl: backjump clause empty"
                            | (Disjunction ([y]), []) -> (formula, formula_mod, xs, cdl, bj_up_map, bj_state, false)
                            | (Disjunction (ys), []) -> (formula_new, formula_mod, xs, cdl, bj_up_map, bj_state, false)
                            | (_, cfs) -> if cdl < 1 
                                          then (formula, formula_mod, Assignment ([]), cdl, bj_up_map, bj_state, false)
                                          else backjump_cdcl_list formula_new xs bj_up_map checkpoints cdl (hd cf) i_map inv_map bj_state 
                       )
                | _ -> if cdl < 1
                       then (formula, formula_mod, Assignment ([]), cdl, bj_up_map, bj_state, false)
                       else (
                             match (bj_clause, cf) with
                                | (_, []) -> ((learn formula_new (clauselist_to_neg_clause (convert_unsat_core_i bj_u_core i_map inv_map))), formula_mod, xs, cdl, bj_up_map, bj_state, true)
                                | (_, cfs) -> backjump_cdcl_list (learn formula_new (clauselist_to_neg_clause (convert_unsat_core_i bj_u_core i_map inv_map))) xs bj_up_map checkpoints cdl (hd cf) i_map inv_map bj_state 
                            )
            );;

let rec dpll_inc_i_list_rec assignment formula formula_mod up_map s_state checkpoints i_map inv_map dl conf_count =
            let new_cps = checkpoints @ [(dl, Simplex_inc.checkpoint_simplex s_state)] in
                match decision_inc_i_list assignment formula_mod up_map s_state i_map inv_map dl conf_count with
                     (* This match means there was no literal to use for decision, hence dpll found a potential model *)
                    | (_, _, _, _, _, _, _, true) -> (
                        match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) s_state with
                            | Simplex_inc.Inl (unsat_core) -> if dl < 1
                                                            then (false)
                                                            else let (num, cp) = hd (checkpoints) in
                                                                  let r_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                   (
                                                                    match length unsat_core with 
                                                                        | 0 -> failwith "[Invalid argument] unsat core empty"
                                                                        | 1 -> (
                                                                                match (hd (convert_unsat_core_i unsat_core i_map inv_map)) with
                                                                                    | Atom (y) -> restart_inc_i_list_unit assignment formula up_map r_state [hd (checkpoints)] i_map inv_map y false
                                                                                    | Not (Atom (y)) -> restart_inc_i_list_unit assignment formula up_map r_state [hd (checkpoints)] i_map inv_map y true
                                                                                    | _ -> failwith "[Invalid argument] dpll_inc_i_list_rec: unsat_core does not consist of literals"
                                                                                )
                                                                        | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                                    if conf_count > -1
                                                                                    then (restart_inc_i_list assignment (learn formula (Disjunction (u_core))) up_map r_state [hd (checkpoints)] i_map inv_map)
                                                                                    else (
                                                                                          let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i assignment (Disjunction (u_core)) up_map dl) in 
                                                                                           let cdl = (get_current_decision_level ys) in
                                                                                            let cp = get_checkpoint checkpoints cdl in 
                                                                                             let b_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                                              let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
                                                                                               let formula_new = learn formula bj_clause in
                                                                                                let (new_f_mod, cf) = reconstruct_modifiable_formula formula_new ys in 
                                                                                                 (
                                                                                                  match (length bj_u_core) with
                                                                                                    | 0 -> ( 
                                                                                                            match (bj_clause, cf) with
                                                                                                                | (Disjunction ([]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                | (Disjunction ([v]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                | (Disjunction (vs), []) -> dpll_inc_i_list_rec ys formula_new new_f_mod bj_up_map bj_state (reset_checkpoints checkpoints cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                | (_, cfs) -> (
                                                                                                                               match backjump_to_conflictless_state formula ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                                                                | ([], _, _, _, _, _) -> false 
                                                                                                                                | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                                                       let (n_f_mod, _) = reconstruct_modifiable_formula formula_new (Assignment (bj_cons_assignment)) in
                                                                                                                                        dpll_inc_i_list_rec (Assignment (bj_cons_assignment)) formula_new n_f_mod bj_cons_up_map bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                                                              )
                                                                                                                | _ -> failwith "[Invalid argument] dpll_inc_i_list_rec: backjump clause not a clause"
                                                                                                           )
                                                                                                    | _ -> (
                                                                                                            match backjump_to_t_consistent_state ys bj_up_map checkpoints i_map inv_map cdl b_state with 
                                                                                                                | ([], _, _, _, _, _) -> false
                                                                                                                | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) ->
                                                                                                                    let (n_f_mod, _) = reconstruct_modifiable_formula formula_new (Assignment (cons_assignment)) in
                                                                                                                        dpll_inc_i_list_rec (Assignment (cons_assignment)) formula_new n_f_mod cons_up_map cons_state cons_cps i_map inv_map cons_dl (conf_count + 1)
                                                                                                           )

                                                                                                 )
                                                                                         )
                                                                        )
                                                                                                
                            | Simplex_inc.Inr (n_state) -> true
                        )
                | (new_assignment, new_formula_mod, new_dl, new_up_map, new_state, prop, conf, false) ->
                    (
                     match conf with 
                        | [] -> (
                                 match prop with
                                    | [] -> dpll_inc_i_list_rec new_assignment formula new_formula_mod new_up_map new_state new_cps i_map inv_map new_dl (conf_count)
                                    | x :: xs -> let (n_assignment, n_formula_mod, n_up_map, n_state, n_conf) = unit_propagation_inc_i_list new_assignment new_formula_mod new_up_map new_state i_map inv_map prop new_dl in 
                                                    (
                                                     match n_conf with
                                                      | [] -> (
                                                                match Simplex_inc.check_simplex (Simplex_inc.equal_nat, Simplex_inc.linorder_nat) n_state with
                                                                    | Inl (unsat_core) -> let (num, cp) = hd (checkpoints) in
                                                                                          let r_state = Simplex_inc.backtrack_simplex cp n_state in
                                                                                          (
                                                                                           match length unsat_core with 
                                                                                            | 0 -> failwith "[Invalid argument] unsat core empty"
                                                                                            | 1 -> (
                                                                                                    match (hd (convert_unsat_core_i unsat_core i_map inv_map)) with
                                                                                                        | Atom (y) -> restart_inc_i_list_unit new_assignment formula n_up_map r_state [hd (checkpoints)] i_map inv_map y false
                                                                                                        | Not (Atom (y)) -> restart_inc_i_list_unit new_assignment formula n_up_map r_state [hd (checkpoints)] i_map inv_map y true
                                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: unsat_core does not consist of literals"
                                                                                                   )
                                                                                            | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in 
                                                                                                    if conf_count > -1
                                                                                                    then (restart_inc_i_list assignment (learn formula (Disjunction (u_core))) n_up_map r_state [hd (checkpoints)] i_map inv_map)
                                                                                                    else (
                                                                                                          let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i n_assignment (Disjunction (u_core)) n_up_map new_dl) in 
                                                                                                           let cdl = (get_current_decision_level ys) in
                                                                                                            let cp = get_checkpoint new_cps cdl in 
                                                                                                             let b_state = Simplex_inc.backtrack_simplex cp s_state in
                                                                                                              let (bj_state, bj_u_core) = assert_backjump l i_map inv_map b_state in
                                                                                                               let formula_new = learn formula bj_clause in
                                                                                                                let (new_f_mod, cf) = reconstruct_modifiable_formula formula_new ys in 
                                                                                                                 (
                                                                                                                  match (length bj_u_core) with
                                                                                                                    | 0 -> (
                                                                                                                            match (bj_clause, cf) with
                                                                                                                                | (Disjunction ([]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                                | (Disjunction ([v]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                                | (Disjunction (vs), []) -> dpll_inc_i_list_rec ys formula_new new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                                                                                                | (_, cfs) -> if cdl < 1 
                                                                                                                                              then false 
                                                                                                                                              else (
                                                                                                                                                    match backjump_to_conflictless_state formula ys bj_up_map new_cps cdl i_map inv_map bj_state with 
                                                                                                                                                        | ([], _, _, _, _, _) -> false 
                                                                                                                                                        | (bj_cons_assignment, bj_cons_up_map, bj_cons_cps, bj_cons_state, bj_cons_dl, bj_cons_l) ->
                                                                                                                                                                 let (n_f_mod, _) = reconstruct_modifiable_formula formula_new (Assignment (bj_cons_assignment)) in
                                                                                                                                                                    dpll_inc_i_list_rec (Assignment (bj_cons_assignment)) formula_new n_f_mod bj_cons_up_map bj_cons_state bj_cons_cps i_map inv_map bj_cons_dl (conf_count + 1)
                                                                                                                                                    )
                                                                                                                                | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                                                            )
                                                                                                                    | _ -> (
                                                                                                                            match backjump_to_t_consistent_state ys bj_up_map new_cps i_map inv_map cdl b_state with 
                                                                                                                                | ([], _, _, _, _, _) -> false 
                                                                                                                                | (cons_assignment, cons_up_map, cons_cps, cons_state, cons_dl, cons_l) ->
                                                                                                                                       let (n_f_mod, _) = reconstruct_modifiable_formula formula_new (Assignment (cons_assignment)) in
                                                                                                                                        dpll_inc_i_list_rec (Assignment (cons_assignment)) formula_new n_f_mod cons_up_map cons_state cons_cps i_map inv_map cons_dl (conf_count + 1)
                                                                                                                           )

                                                                                                                 )
                                                                                                    )
                                                                                          )
                                                                    | Inr (state) -> dpll_inc_i_list_rec n_assignment formula n_formula_mod n_up_map state new_cps i_map inv_map new_dl (conf_count)
                                                               )
                                                      | z :: zs -> ( 
                                                                    let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i n_assignment (hd n_conf) n_up_map new_dl) in 
                                                                     let cdl = (get_current_decision_level ys) in
                                                                      let cp = get_checkpoint new_cps cdl in 
                                                                       let b_state = Simplex_inc.backtrack_simplex cp n_state in
                                                                        let (bj_state, unsat_core) = assert_backjump l i_map inv_map b_state in
                                                                         let (num, cp_0) = hd (new_cps) in
                                                                          let r_state = Simplex_inc.backtrack_simplex cp_0 bj_state in
                                                                           let formula_new = learn formula bj_clause in
                                                                            let (new_f_mod, cf) = reconstruct_modifiable_formula formula_new ys in 
                                                                             (
                                                                              match (length unsat_core) with
                                                                                | 0 -> (
                                                                                        match (bj_clause, cf) with
                                                                                        | (Disjunction ([]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                                                        | (Disjunction ([v]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                                                        | (Disjunction (vs), []) -> dpll_inc_i_list_rec ys formula_new new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                                                        | (Disjunction ([]), cfs) -> failwith "[Invalid argument] backjump clause empty\n";
                                                                                        | (Disjunction (vs), cfs) -> if cdl < 1 
                                                                                                                     then (false )
                                                                                                                     else (
                                                                                                                           match (backjump_cdcl_list formula ys bj_up_map new_cps cdl (hd cf) i_map inv_map bj_state) with 
                                                                                                                            | (_, _, Assignment ([]), _, _, _, _) -> false 
                                                                                                                            | (formula_cdcl, f_mod_cdcl, assignment_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, true) -> 
                                                                                                                                restart_inc_i_list assignment_cdcl formula_cdcl up_map_cdcl r_state [hd (checkpoints)] i_map inv_map
                                                                                                                            | (formula_cdcl, f_mod_cdcl, assignment_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, false) ->
                                                                                                                                dpll_inc_i_list_rec assignment_cdcl formula_cdcl f_mod_cdcl up_map_cdcl state_cdcl (reset_checkpoints new_cps cdl) i_map inv_map dl_cdcl (conf_count + 1)
                                                                                                                          )
                                                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                                                       )
                                                                            | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in
                                                                                   restart_inc_i_list assignment (learn formula_new (Disjunction (u_core))) bj_up_map r_state [hd (checkpoints)] i_map inv_map
                                                                             )
                                                                   )
                                                    )
                                )
                        | x :: xs -> 
                                    (
                                     let (ys, l, bj_clause, bj_up_map) = (backjump_twl_i new_assignment (hd conf) new_up_map new_dl) in 
                                      let cdl = (get_current_decision_level ys) in
                                       let cp = get_checkpoint new_cps cdl in 
                                        let b_state = Simplex_inc.backtrack_simplex cp new_state in 
                                         let (bj_state, unsat_core) = assert_backjump l i_map inv_map b_state in
                                          let (num, cp_0) = hd (new_cps) in
                                           let r_state = Simplex_inc.backtrack_simplex cp_0 bj_state in
                                            let formula_new = learn formula bj_clause in
                                             let (new_f_mod, cf) = reconstruct_modifiable_formula formula_new ys in 
                                              (
                                               match (length unsat_core) with
                                                | 0 -> (
                                                        match (bj_clause, cf) with
                                                        | (Disjunction ([]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                        | (Disjunction ([v]), []) -> dpll_inc_i_list_rec ys formula new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                        | (Disjunction (vs), []) -> dpll_inc_i_list_rec ys formula_new new_f_mod bj_up_map bj_state (reset_checkpoints new_cps cdl) i_map inv_map cdl (conf_count + 1)
                                                        | (Disjunction ([]), cfs) -> failwith "[Invalid argument] backjump clause empty\n"; 
                                                        | (Disjunction (vs), cf) -> if cdl < 1 
                                                                                    then (false)
                                                                                    else ( 
                                                                                          match (backjump_cdcl_list formula ys bj_up_map new_cps cdl (hd cf) i_map inv_map bj_state) with 
                                                                                            | (_, _, Assignment ([]), _, _, _, _) -> false 
                                                                                            | (formula_cdcl, f_mod_cdcl, assignment_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, true) -> 
                                                                                                restart_inc_i_list assignment_cdcl formula_cdcl up_map_cdcl r_state [hd (checkpoints)] i_map inv_map
                                                                                            | (formula_cdcl, f_mod_cdcl, assignment_cdcl, dl_cdcl, up_map_cdcl, state_cdcl, false) ->
                                                                                                dpll_inc_i_list_rec assignment_cdcl formula_cdcl f_mod_cdcl up_map_cdcl state_cdcl (reset_checkpoints new_cps cdl) i_map inv_map dl_cdcl (conf_count + 1)
                                                                                         )
                                                        | _ -> failwith "[Invalid argument] dpll_twl_inc_rec: backjump clause not a clause"
                                                        )
                                                | _ -> let Disjunction (u_core) = clauselist_to_neg_clause (convert_unsat_core_i unsat_core i_map inv_map) in
                                                            restart_inc_i_list assignment (learn formula_new (Disjunction (u_core))) bj_up_map r_state [hd (checkpoints)] i_map inv_map
                                            )
                                    )         
                    
                    )

and dpll_inc_i_list formula up_map i_map inv_map s_state checkpoints = 
                let (new_formula, new_assignment, new_up_map, prop, conf_unit, new_state, _) = preprocess_unit_clauses_inc_i (Assignment ([])) formula up_map s_state i_map inv_map in 
                        (*Printing.print_formula new_formula; printf "\n\n"; *)
                        if conf_unit 
                        then false
                        else (
                              let (f_mod, _) = reconstruct_modifiable_formula new_formula new_assignment in
                               let (n_assignment, n_f_mod, n_up_map, n_state, conf) = unit_propagation_inc_i_list new_assignment f_mod new_up_map new_state i_map inv_map prop 0 in 
                                    (
                                     match conf with
                                        | [] -> dpll_inc_i_list_rec n_assignment new_formula n_f_mod n_up_map n_state checkpoints i_map inv_map 0 0
                                        | x :: xs -> false
                                    )
                            )

and restart_inc_i_list assignment formula up_map s_state checkpoints i_map inv_map = 
                        (*Printing.print_assignment assignment; printf "\n\n";*) (*printf "RESTART\n";*)  let (new_formula, new_assignment, new_up_map, prop, conf_unit, new_state, _) = preprocess_unit_clauses_inc_i (preserve_unit_assignments assignment) formula up_map s_state i_map inv_map in 
                            if conf_unit
                            then (false)
                            else ( let (ra_state, ra_conf, _) = reassert_after_restart new_assignment i_map inv_map new_state in
                                    (*printf "POST_REASSERT\n\n";*) (
                                     if length ra_conf > 0
                                     then (false)
                                     else (
                                          let (f_mod, _) = reconstruct_modifiable_formula new_formula new_assignment in
                                           let (n_assignment, n_f_mod, n_up_map, n_state, conf) = unit_propagation_inc_i_list new_assignment f_mod new_up_map ra_state i_map inv_map prop 0 in 
                                                (
                                                match conf with
                                                    | [] -> dpll_inc_i_list_rec n_assignment new_formula n_f_mod n_up_map n_state checkpoints i_map inv_map 0 0
                                                    | x :: xs -> false
                                                )
                                          )
                                    )
                                 )
                                                
and restart_inc_i_list_unit assignment formula up_map s_state checkpoints i_map inv_map unit_literal lit_val = 
                        (*printf "RESTART_UNIT\n";*) let (new_formula, new_assignment, new_up_map, prop, conf_unit, new_state, _) = preprocess_unit_clauses_inc_i (preserve_unit_assignments assignment) formula up_map s_state i_map inv_map in
                            if conf_unit
                            then false
                            else (
                                  let (ra_state, ra_conf, _) = reassert_after_restart new_assignment i_map inv_map new_state in
                                    (*printf "POST_REASSERT\n\n";*) (
                                     if length ra_conf > 0
                                     then (false)
                                     else ( 
                                           let Assignment (xs) = new_assignment in
                                            if (is_assigned_i new_assignment (Atom (unit_literal)))
                                            then false
                                            else (
                                                  let (f_mod, _) = reconstruct_modifiable_formula new_formula (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) in
                                                  let (n_assignment, n_f_mod, n_up_map, n_state, conf) = unit_propagation_inc_i_list (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) f_mod new_up_map ra_state i_map inv_map prop 0 in
                                                  (
                                                   match conf with
                                                    | [] -> dpll_inc_i_list_rec n_assignment new_formula n_f_mod n_up_map n_state checkpoints i_map inv_map 0 0
                                                    | x :: xs -> false
                                                  )
                                                 )
                                          )
                                    )
                                 );;

let sat_inc_i_list (formula, cs, i_map, inv_map) =
    let (tableau, cs) = (Util.to_simplex_format_inc_init cs i_map) in
     let state = Simplex_inc.init_simplex Simplex_inc.linorder_nat tableau in
       match (dpll_inc_i_list formula UP_Map.empty i_map inv_map state [(-1, Simplex_inc.checkpoint_simplex state)]) with 
        | true -> printf "SAT "
        | false -> printf "UNSAT ";;

let sat_inc_i (formula, cs, i_map, inv_map, vsids) =
   let (tableau, cs) = (Util.to_simplex_format_inc_init cs i_map) in
    (*Printing.print_simplex_constraints_inc tableau;*)
    let state = Simplex_inc.init_simplex Simplex_inc.linorder_nat tableau in
    match (dpll_twl_inc_i formula UP_Map.empty i_map inv_map state [(-1, Simplex_inc.checkpoint_simplex state)]) with
        | true -> printf "SAT "
        | false -> printf "UNSAT ";; 

let sat_inc (formula, cs, i_map, inv_map) =
   let (tableau, cs) = (Util.to_simplex_format_inc_init cs i_map) in
    let state = Simplex_inc.init_simplex Simplex_inc.linorder_nat tableau in
    match (dpll_twl_inc formula UP_Map.empty i_map inv_map state [(-1, Simplex_inc.checkpoint_simplex state)]) with
        | true -> printf "SAT "
        | false -> printf "UNSAT ";; 


(****************************************************************************************************)

let sat_twl formula = 
    match (dpll_twl formula) with
        | true -> printf "SAT "
        | false -> printf "UNSAT ";; 

let sat formula = 
    match (dpll formula) with
        | true -> printf "SAT "
        | false -> printf "UNSAT ";; 
                               