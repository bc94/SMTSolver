open String
open Types
open List
open Core.Std
open Simplex

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
        | Formula (Conjunction ([])) -> (true, formula, false) 
        | Formula (Conjunction (x :: xs)) -> (
                                              match (is_clause_satisfied assignment x) with 
                                                | true -> model_found assignment (Formula (Conjunction (xs)))
                                                | false -> (
                                                            match (unassigned_or_true assignment x) with
                                                                | [] -> (false, formula, true)
                                                                | _ -> (false, formula, false)
                                                           )
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

let rec unit_propagation assignment formula formula_opt dl =
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
        | _ -> failwith "[Invaid argument] unit_propagation";;

let rec exhaustive_unit_propagation assignment formula dl = 
    let (xs, f_opt) = (unit_propagation assignment formula [] dl) in 
        match (compare xs assignment) with 
            | 0 -> (xs, f_opt)
            | _ -> exhaustive_unit_propagation xs f_opt dl;;

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
        | Formula (Conjunction (x :: xs)) -> decide assignment x dl
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
                                       )
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
                                                                                    | Atom (y) -> ls @ [(y, true, false, dl)]
                                                                                    | Not (Atom (y)) -> ls @ [(y, false, false, dl)]
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
                                let (Disjunction (zs)) = (find_backjump_clause xs formula (hd ys)) in
                                    (
                                     match Disjunction (tl (rev zs)) with 
                                        | Disjunction ([]) -> Assignment (backjump_rec assignment
                                                                            0
                                                                            (Disjunction (zs))
                                                                            [])
                                        | _ ->  Assignment (backjump_rec assignment
                                                            (get_decision_level xs (hd (tl (rev zs)))) 
                                                            (Disjunction (zs))
                                                            [])
                                    )
        | _ -> failwith "[Invalid argument] backjump";;

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
                                                | _ -> backtrack_rec (Assignment (xs)) dl (ls @ [(c, v, d, dl)])
                                             );;

let backtrack assignment dl = Assignment (backtrack_rec assignment dl []);;

(* The actual DPLL procedure *)

(* 'formula' is the actual initial formula and never changes. *)
(* 'formula_opt' is an optimized alternative formula where every *)
(* satisfied clause has been removed to make most of the function *)
(* calls in the procedure more efficient *)
let rec dpll_rec assignment formula formula_opt dl = 
    match (model_found assignment formula_opt) with
        | (true, _, _) -> true
        | (false, formula_new, false) -> (
                                          let (xs, f_opt) = (exhaustive_unit_propagation assignment formula_new dl) in 
                                                 match (compare assignment xs) with
                                                    | 0 -> (
                                                            match (Simplex.simplex (Util.to_simplex_format_init assignment)) with 
                                                                | Some (x) -> (
                                                                               match (decision assignment formula_new dl) with
                                                                                | (ys, l) -> dpll_rec ys formula formula_new l
                                                                              )
                                                                | None -> dpll_rec (backtrack xs dl) formula formula (dl - 1)
                                                           )
                                                    | _ -> dpll_rec xs formula f_opt dl
                                         )
        | (false, formula_new, true) -> ( 
                                         match (has_decision_literals assignment) with 
                                            | false -> false
                                            | true -> let xs = (backjump assignment formula) in dpll_rec xs formula formula (get_current_decision_level xs)
                                        );;
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
                                  );;*)

let dpll formula = dpll_rec (unit (Assignment ([])) formula) formula formula 0;;

let sat formula = 
    match (dpll formula) with
        | true -> printf "SAT\n"
        | false -> printf "UNSAT\n";; 
                               