module TWL_Map = Map.Make(String);;

open String
open Types
open List
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
        | _ -> failwith "[Invalid argument] contains_unassigned_literal: argument neither a close nor a literal";;

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

let is_proper_constraint cons = 
    match cons with 
    | Constraint (x) -> true
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
                                   );;

let rec propagate formula_opt literal acc next_lit conf = 
    match formula_opt with
        | (Formula (Conjunction ([]))) -> ((Formula (Conjunction (acc))), next_lit, conf)
        | (Formula (Conjunction ((Disjunction (x)) :: xs))) -> (
                                                                match (contains_literal x literal) with
                                                                    | Some (true) -> propagate (Formula (Conjunction (xs))) literal acc next_lit conf
                                                                    | Some (false) -> (
                                                                                       match (length x) with
                                                                                        | 1 -> ((Formula (Conjunction (acc))), next_lit, true)
                                                                                        | _ -> let (Disjunction (y)) = (remove_literal (Disjunction (x)) literal []) in
                                                                                                (
                                                                                                 match (length y) with
                                                                                                    | 1 -> propagate (Formula (Conjunction (xs))) literal (acc @ [Disjunction (y)]) y conf
                                                                                                    | _ -> propagate (Formula (Conjunction (xs))) literal (acc @ [Disjunction (y)]) next_lit conf
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
                                     )
        | (f_new, [], false) -> (
                                 let Assignment (xs) = assignment in match literal with
                                    | Atom (x) -> ((Assignment (xs @ [(x, true, false, dl)])), f_new, false)
                                    | Not (Atom (x)) -> ((Assignment (xs @ [(x, false, false, dl)])), f_new, false)
                                )
        | (f_new, next_lit, false) -> (
                                     let Assignment (xs) = assignment in match literal with
                                        | Atom (x) -> exhaustive_propagate (Assignment (xs @ [(x, true, false, dl)])) f_new (hd next_lit) dl
                                        | Not (Atom (x)) -> exhaustive_propagate (Assignment (xs @ [(x, false, false, dl)])) f_new (hd next_lit) dl
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
                                                                           )
                                                               )
        | _ -> failwith "[Invalid argument] formula not in cnf";;    

let learn formula clause =
    match formula with
        | Formula (Conjunction (xs)) -> Formula (Conjunction ([clause] @ xs))
        | _ -> failwith "[Invalid argument] learn: formula not in CNF";;

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
                                             )
        | _ -> failwith "[Invalid argument] backjump_rec";;

let backjump assignment formula = 
    (*printf "BACKJUMP\n\n";*) match assignment with 
        | Assignment (xs) -> let ys = (find_conflict assignment formula) in
                                let (Disjunction (zs)) = (find_backjump_clause xs formula (hd ys)) in
                                    (
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

let rec check_clause assignment f_map clause literal prop conf = 
    match clause with
        | Disjunction (w1 :: w2 :: ws) -> (
                                           match (compare w1 literal) with
                                            | 0 -> if is_true assignment w2 
                                                   then (f_map, prop, conf)
                                                   else (
                                                         if is_assigned assignment w2 
                                                         then (f_map, prop, [clause])
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
                                                                    then (f_map, prop, [clause])
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

let rec update_clauses assignment f_map clauses literal prop conf = 
    match clauses with
        | [] -> (f_map, prop, conf)
        | x :: xs -> let (new_map, new_prop, new_conf) = (check_clause assignment f_map x literal prop conf) in 
                        update_clauses assignment new_map xs literal new_prop new_conf;;

(* NOTE: literal should always be the negation of the literal that was just assigned *)
(*       This function then updates the watch list of the negated literal *)
let update_watch_lists assignment f_map literal = update_clauses assignment f_map (TWL_Map.find (Printing.print_element literal) f_map) literal [] [];;

let rec choose_decision_literal assignment clause = 
    match clause with
        | Disjunction ([]) -> failwith "[Invalid argument] choose_decision_literal: clause does not contain a literal suited for decision"
        | Disjunction (x :: xs) -> if is_assigned assignment x 
                                   then choose_decision_literal assignment (Disjunction (xs))
                                   else x;;

let rec decision_twl formula assignment f_map dl =
    let Formula (Conjunction (cs)) = formula in 
     match contains_unassigned_literal assignment (hd cs) with
        | false -> decision_twl (Formula (Conjunction (tl cs))) assignment f_map dl
        | true -> (
                    let Assignment (xs) = assignment in
                     match choose_decision_literal assignment (hd cs) with
                        | Atom (x) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Not (Atom (x))) in 
                                        (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, prop, conf)
                        | Not (Atom (x)) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Atom (x)) in
                                                (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, prop, conf) 
                   );;

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
        | Assignment (xs) -> let (Disjunction (ys)) = (find_backjump_clause xs formula conf) in
                                    (
                                     match (length ys) with 
                                        | 0 -> (Assignment (backjump_rec assignment
                                                                          0
                                                                          (Disjunction (ys))
                                                                          []),
                                                 Disjunction (ys))
                                        | 1 -> (Assignment (backjump_rec assignment
                                                                          0
                                                                          (Disjunction (ys))
                                                                          []),
                                                 Disjunction (ys))
                                        | _ ->  (Assignment (backjump_rec assignment
                                                            (get_decision_level xs (hd (tl (rev ys)))) 
                                                            (Disjunction (ys))
                                                            []),
                                                Disjunction (ys))
                                    )
        | _ -> failwith "[Invalid argument] backjump_twl";;

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
        | _ -> failwith "[Invalid argument] add_clause_to_map: argument not a clause";;

let construct_map formula = add_all_keys formula formula TWL_Map.empty [];;

(* removes unit clauses from the formula *)
let rec preprocess_unit_clauses_rec formula new_formula new_assignment prop = 
    match formula with 
        | Formula (Conjunction ([])) -> (Formula (Conjunction (new_formula)), Assignment (new_assignment), prop)
        | Formula (Conjunction (x :: xs)) -> (
                                              match x with 
                                                | Disjunction (ys) -> preprocess_unit_clauses_rec (Formula (Conjunction (xs))) (new_formula @ [x]) new_assignment prop
                                                | Atom (y) -> preprocess_unit_clauses_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, true, false, 0)]) (prop @ [x])
                                                | Not (Atom (y)) -> preprocess_unit_clauses_rec (Formula (Conjunction (xs))) new_formula (new_assignment @ [(y, false, false, 0)]) (prop @ [x])
                                             );;

let preprocess_unit_clauses (Assignment (assignment)) formula = preprocess_unit_clauses_rec formula [] assignment [];;

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
                                                | Some (x) -> (
                                                               match x with
                                                                | Mapping (RBT (Empty)) -> printf "Maybe\n"; true
                                                                | Mapping (RBT (_)) -> true
                                                              )
                                                | None -> (
                                                           match cs with 
                                                            | Assignment ([z]) -> (
                                                                                   match z with
                                                                                    | (y, true, d, l) -> restart_twl_unit assignment formula f_map literals y false
                                                                                    | (y, false, d, l) -> restart_twl_unit assignment formula f_map literals y true
                                                                                  )
                                                            | Assignment (zs) -> let ys = (Disjunction (transform_to_neg_clause cs)) in 
                                                                                    printf "restart\n\n"; restart_twl assignment (learn formula ys) (add_clause_to_map f_map ys) literals
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
                                                                                            (*Printing.print_assignment n_assignment; printf "\n\n";*) (*Printing.print_simplex_constraints sf_assignment;*)
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
                                                                                                                                        printf "restart\n\n"; restart_twl n_assignment (learn formula ys) (add_clause_to_map f_map ys) literals
                                                                                                          )
                                                                                            )
                                                              )
                                                      | x :: xs -> (
                                                                    let (ys, bj_clause) = (backjump_twl n_assignment formula (hd n_conf)) in 
                                                                        (
                                                                         printf "backjump\n\n"; match (bj_clause, (conflict_exists ys formula)) with
                                                                            | (_, true) -> false
                                                                            | (Disjunction ([]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                                                            | (Disjunction ([z]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                                                            | (Disjunction (zs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_rec ys formula_l (add_clause_to_map new_map bj_clause) literals (get_current_decision_level ys)
                                                                        )
                                                                   )
                                                    )
                                )
                        | x :: xs -> (
                                      let (ys, bj_clause) = (backjump_twl new_assignment formula (hd conf)) in 
                                        (
                                         printf "backjump\n\n"; match (bj_clause, (conflict_exists ys formula)) with
                                            | (_, true) -> false
                                            | (Disjunction ([]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                            | (Disjunction ([z]), false) -> dpll_twl_rec ys formula new_map literals (get_current_decision_level ys)
                                            | (Disjunction (zs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_rec ys formula_l (add_clause_to_map new_map bj_clause) literals (get_current_decision_level ys)
                                        )
                                     )
                                      
                    )

and dpll_twl formula = let (new_formula, new_assignment, prop) = preprocess_unit_clauses (Assignment ([])) formula in 
                        (*Printing.print_formula new_formula; printf "\n\n";*) let (f_map, literals) = construct_map new_formula in 
                            let (n_assignment, n_map, conf) = unit_propagation_twl new_assignment f_map prop 0 in 
                                (
                                 match conf with
                                    | [] -> dpll_twl_rec n_assignment new_formula n_map literals 0
                                    | x :: xs -> false
                                )

and restart_twl assignment formula f_map literals = let (new_formula, new_assignment, prop) = preprocess_unit_clauses (preserve_unit_assignments assignment) formula in 
                                            let (n_assignment, n_map, conf) = unit_propagation_twl new_assignment f_map prop 0 in 
                                                (
                                                 match conf with
                                                    | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) dpll_twl_rec n_assignment new_formula n_map literals 0
                                                    | x :: xs -> false
                                                )
                                                
and restart_twl_unit assignment formula f_map literals unit_literal lit_val = let (new_formula, new_assignment, prop) = preprocess_unit_clauses (preserve_unit_assignments assignment) formula in
                                                            let (n_assignment, n_map, conf) = let Assignment (xs) = new_assignment in unit_propagation_twl (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) f_map prop 0 in 
                                                                (
                                                                 match conf with
                                                                    | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) dpll_twl_rec n_assignment new_formula n_map literals 0
                                                                    | x :: xs -> false
                                                                );;

(**********************************************)

(****************************************************************************************************)
(* Two-watched-literal implementation using incremental simplex, unsat cores and theory propagation *)
(****************************************************************************************************)

let rec convert_unsat_core_rec unsat_core inv_map result =
    match unsat_core with
        | [] -> result
        | x :: xs -> (
                      match (Tseiting.Index_Map.find x inv_map) with
                        | (y, true, _, _) -> convert_unsat_core_rec xs inv_map (result @ (Atom (y)))
                        | (y, false, _, _) -> convert_unsat_core_rec xs inv_map (result @ (Not (Atom (y))))
                     );;

let convert_unsat_core unsat_core = convert_unsat_core_rec unsat_core inv_map [];;

let rec decision_twl_inc formula assignment f_map s_state i_map inv_map dl =
    let Formula (Conjunction (cs)) = formula in 
     match contains_unassigned_literal assignment (hd cs) with
        | false -> decision_twl (Formula (Conjunction (tl cs))) assignment f_map s_state i_map inv_map dl
        | true -> (
                    let Assignment (xs) = assignment in
                     match choose_decision_literal assignment (hd cs) with
                        | Atom (x) -> if is_proper_constraint x
                                      then (
                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat Simplex_inc.lrv_QDelta Simplex_inc.equal_QDelta (Tseitin.Index_Map.find (Printing.print_constraint_n x) i_map) s_state with
                                                | Inl (unsat_core) -> (Assignment (xs @ [(x, true, true, dl + 1)]), f_map, dl + 1, s_state, convert_unsat_core (unsat_core) inv_map)
                                                | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Not (Atom (x))) in 
                                                                    (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, n_state, prop, conf)
                                           )
                                      else (  
                                            let (new_map, prop, conf) = update_watch_lists assignment f_map (Not (Atom (x))) in 
                                                (Assignment (xs @ [(x, true, true, dl + 1)]), new_map, dl + 1, s_state, prop, conf)
                                           )
                        | Not (Atom (x)) -> if is_proper constraint x
                                            then (
                                                  match Simplex_inc.assert_simplex Simplex_inc.equal_nat Simplex_inc.lrv_QDelta Simplex_inc.equal_QDelta (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n x) i_map) s_state with
                                                    | Inl (unsat_core) -> (Assignment (xs @ [(x, false, true, dl + 1)]), f_map, dl + 1, s_state, convert_unsat_core (unsat_core) inv_map)
                                                    | Inr (n_state) -> let (new_map, prop, conf) = update_watch_lists assignment f_map (Atom (x)) in 
                                                                            (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, n_state, prop, conf)
                                                 )
                                            else (
                                                  let (new_map, prop, conf) = update_watch_lists assignment f_map (Atom (x)) in
                                                    (Assignment (xs @ [(x, false, true, dl + 1)]), new_map, dl + 1, prop, conf) 
                                                 )
                   );;

let rec unit_propagation_twl_inc assignment f_map s_state i_map inv_map prop dl = 
    (*printf "PROPAGATION\n\n";*) match prop with 
        | [] -> (assignment, f_map, s_state, [])
        | x :: xs -> (
                      let Assignment (ys) = assignment in 
                       match x with
                        | Atom (y) -> if is_proper_constraint y 
                                      then (
                                            match Simplex_inc.assert_simplex Simplex_inc.equal_nat Simplex_inc.lrv_QDelta Simplex_inc.equal_QDelta (Tseitin.Index_Map.find (Printing.print_constraint_n y) i_map) s_state with
                                                | Inl (unsat_core) -> (assignment, f_map, s_state, convert_unsat_core (unsat_core) inv_map)
                                                | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Not (Atom (y))) in 
                                                                    (
                                                                    match conf with 
                                                                        | [] -> unit_propagation_twl_inc (Assignment (ys @ [(y, true, false, dl)])) new_map n_state i_map (xs @ new_prop) dl
                                                                        | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_map, s_state, z :: zs)
                                                                    )
                                            )
                                      else (
                                            let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Not (Atom (y))) in 
                                            (
                                            match conf with 
                                                | [] -> unit_propagation_twl_inc (Assignment (ys @ [(y, true, false, dl)])) new_map s_state i_map (xs @ new_prop) dl
                                                | z :: zs -> ((Assignment (ys @ [(y, true, false, dl)])), new_map, s_state, z :: zs)
                                            )
                                           )
                        | Not (Atom (y)) -> if is_proper_constraint y 
                                                then (
                                                        match Simplex_inc.assert_simplex Simplex_inc.equal_nat Simplex_inc.lrv_QDelta Simplex_inc.equal_QDelta (Tseitin.Index_Map.find ("-" ^ (Printing.print_constraint_n y)) i_map) s_state with
                                                            | Inl (unsat_core) -> (assignment, f_map, s_state, convert_unsat_core (unsat_core) inv_map)
                                                            | Inr (n_state) -> let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Atom (y)) in 
                                                                                ( 
                                                                                match conf with
                                                                                    | [] -> unit_propagation_twl (Assignment (ys @ [(y, false, false, dl)])) new_map n_state i_map (xs @ new_prop) dl
                                                                                    | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_map, z :: zs)
                                                                                )
                                                        )
                                                else (
                                                      let (new_map, new_prop, conf) = update_watch_lists assignment f_map (Atom (y)) in 
                                                        ( 
                                                        match conf with
                                                            | [] -> unit_propagation_twl (Assignment (ys @ [(y, false, false, dl)])) new_map s_state i_map (xs @ new_prop) dl
                                                            | z :: zs -> ((Assignment (ys @ [(y, false, false, dl)])), new_map, z :: zs)
                                                        )
                                                    )
                        | _ -> failwith "[Invalid argument] unit_propagation_twl: list of propagation literals contains a non-literal element"
                     );;

let rec dpll_twl_inc_rec assignment formula f_map s_state checkpoints i_map inv_map dl = 
    (*Printing.print_assignment assignment; printf "\n\n";*) match model_found_twl assignment formula with
        | true -> (
                   (*Printing.print_assignment assignment; printf "\n\n";*) (*Printing.print_simplex_constraints sf_assignment;*) 
                   match Simplex_inc.check_simplex Simplex_inc.equal_nat Simplex_inc.linorder_nat s_state with
                    | Simplex_inc.Inl (unsat_core) -> let ys = (Disjunction (transform_to_neg_clause (convert_unsat_core unsat_core inv_map))) in 
                                                        printf "restart\n\n"; restart_twl_inc assignment (learn formula ys) (add_clause_to_map f_map ys) s_state i_map inv_map
                    | Simplex_inc.Inr (n_state) -> (* According to my understanding this is sufficient info to determine that formula is SAT *)
                                                    true
                  )
        | false -> let (new_assignment, new_map, new_dl, new_state, prop, conf) = decision_twl_inc formula assignment f_map s_state i_map inv_map dl in 
                    (
                     match conf with 
                        | [] -> (
                                 match prop with
                                    | [] -> dpll_twl_inc_rec new_assignment formula new_map new_state i_map inv_map new_dl
                                    (* TODO: asserts for every atom in unit_propagation and check before the recursive call *)
                                    | x :: xs -> let (n_assignment, n_map, n_state n_conf) = unit_propagation_twl_inc new_assignment new_map new_state i_map inv_map prop new_dl in 
                                                    (
                                                     match n_conf with
                                                      | [] -> (
                                                               (* TODO: check_simplex *)
                                                               match (Util.to_simplex_format_inc_init n_assignment i_map) with 
                                                                    | (sf_assignment, cs) -> ( 
                                                                                            (*Printing.print_assignment n_assignment; printf "\n\n";*) (*Printing.print_simplex_constraints sf_assignment;*)
                                                                                             match Simplex.simplex sf_assignment with
                                                                                                | Some (x) -> dpll_twl_inc_rec n_assignment formula n_map s_state i_map new_dl
                                                                                                | None -> (
                                                                                                            match cs with 
                                                                                                                | Assignment ([z]) -> (
                                                                                                                                       match z with
                                                                                                                                        | (y, true, d, l) -> restart_twl_inc_unit n_assignment formula f_map s_state i_map y false
                                                                                                                                        | (y, false, d, l) -> restart_twl_inc_unit n_assignment formula f_map s_state i_map y true
                                                                                                                                      )
                                                                                                                | Assignment (zs) -> let ys = (Disjunction (transform_to_neg_clause cs)) in 
                                                                                                                                        printf "restart\n\n"; restart_inc_twl n_assignment (learn formula ys) (add_clause_to_map f_map ys) s_state i_map
                                                                                                          )
                                                                                            )
                                                              )
                                                      | x :: xs -> (
                                                                    (* TODO: backjump using simplex checkpoints *)
                                                                    let (ys, bj_clause) = (backjump_twl n_assignment formula (hd n_conf)) in 
                                                                        (
                                                                         printf "backjump\n\n"; match (bj_clause, (conflict_exists ys formula)) with
                                                                            | (_, true) -> false
                                                                            | (Disjunction ([]), false) -> dpll_twl_inc_rec ys formula new_map s_state i_map (get_current_decision_level ys)
                                                                            | (Disjunction ([z]), false) -> dpll_twl_inc_rec ys formula new_map s_state i_map (get_current_decision_level ys)
                                                                            | (Disjunction (zs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_inc_rec ys formula_l (add_clause_to_map new_map bj_clause) s_state i_map (get_current_decision_level ys)
                                                                        )
                                                                   )
                                                    )
                                )
                        | x :: xs -> (
                                      let (ys, bj_clause) = (backjump_twl new_assignment formula (hd conf)) in 
                                        (
                                         printf "backjump\n\n"; match (bj_clause, (conflict_exists ys formula)) with
                                            | (_, true) -> false
                                            | (Disjunction ([]), false) -> dpll_twl_inc_rec ys formula new_map s_state i_map (get_current_decision_level ys)
                                            | (Disjunction ([z]), false) -> dpll_twl_inc_rec ys formula new_map s_state i_map (get_current_decision_level ys)
                                            | (Disjunction (zs), false) -> let formula_l = (learn formula bj_clause) in dpll_twl_inc_rec ys formula_l (add_clause_to_map new_map bj_clause) s_state i_map (get_current_decision_level ys)
                                        )
                                     )
                                      
                    )

and dpll_twl_inc formula i_map inv_map s_state = let (new_formula, new_assignment, prop) = preprocess_unit_clauses (Assignment ([])) formula in 
                        (*Printing.print_formula new_formula; printf "\n\n";*) let (f_map, literals) = construct_map new_formula in 
                            let (n_assignment, n_map, conf) = unit_propagation_twl new_assignment f_map prop 0 in 
                                (
                                 match conf with
                                    | [] -> dpll_twl_inc_rec n_assignment new_formula n_map s_state [] i_map inv_map 0
                                    | x :: xs -> false
                                )

and restart_twl_inc assignment formula f_map s_state i_map inv_map = let (new_formula, new_assignment, prop) = preprocess_unit_clauses (preserve_unit_assignments assignment) formula in 
                                                                let (n_assignment, n_map, conf) = unit_propagation_twl new_assignment f_map prop 0 in 
                                                                    (
                                                                    match conf with
                                                                        | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) dpll_twl_inc_rec n_assignment new_formula n_map s_state [] i_map inv_map 0
                                                                        | x :: xs -> false
                                                                    )
                                                
and restart_twl_inc_unit assignment formula f_map s_state i_map inv_map unit_literal lit_val = let (new_formula, new_assignment, prop) = preprocess_unit_clauses (preserve_unit_assignments assignment) formula in
                                                                                            let (n_assignment, n_map, conf) = let Assignment (xs) = new_assignment in unit_propagation_twl (Assignment (xs @ [(unit_literal, lit_val, false, 0)])) f_map prop 0 in 
                                                                                                (
                                                                                                match conf with
                                                                                                    | [] -> (*Printing.print_formula new_formula; printf "\n\n";*) dpll_twl_inc_rec n_assignment new_formula n_map s_state [] i_map inv_map  0
                                                                                                    | x :: xs -> false
                                                                                                );;

let sat_inc formula cs i_map inv_map =
    let state = Simplex_inc.init_simplex Simplex_inc.linorder_nat (Util.to_simplex_format_inc_init cs i_map) in
    match (dpll_twl_inc formula i_map inv_map state) with
        | true -> printf "SAT\n"
        | false -> printf "UNSAT\n";; 

(****************************************************************************************************)

let sat formula = 
    match (dpll_twl formula) with
        | true -> printf "SAT\n"
        | false -> printf "UNSAT\n";; 
                               