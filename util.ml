open Types
open Simplex
open Big_int

(* Print execution time of function 'f' applied to argument 'x' *)

let time f x =
    let start = Unix.gettimeofday ()
    in let res = f x
    in let stop = Unix.gettimeofday ()
    in let () = Printf.printf "Time: %fs\n%!" (stop -. start)
    in
       res;;

let rec is_in_varlist varlist var = 
    match varlist with
        | [] -> -1
        | (v, n) :: xs -> (
                           match (compare v var) with
                            | 0 -> n
                            | _ -> is_in_varlist xs var
                          );;

(* Takes a sum without Nums in it and multiplies every list element with -1. *)
(* This is needed when moving sums from one side to the other in a constraint *)
let rec negate_sum_vars sum = 
    match sum with 
        | Sum ([]) -> []
        | Sum (x :: xs) -> (
                            match x with 
                                | Var (y) -> [Prod ([Num (-1); Var (y)])] @ (negate_sum_vars (Sum xs))
                                | Prod (p) -> (
                                               match p with 
                                                | [Var (y); Num (n)] -> [Prod ([Var (y); Num (n * (-1))])] @ (negate_sum_vars (Sum xs))
                                                | [Num (n); Var (y)] -> [Prod ([Num (n * (-1)); Var (y)])] @ (negate_sum_vars (Sum xs))
                                                | _ -> failwith "[Invalid argument] negate_sum_vars: product 'Prod (p)' has more than 2 list elements. Variables are limited to one coefficient."
                                              )
                                | Num (n) -> failwith "[Invalid argument] negate_sum_vars: this function should only be called with Sum (x), where x contains only Vars and Prods"
                                | Sum (y) -> failwith "[Invalid argument] argument has form 'Sum (Sum (xs))'. This should not happen if it was parsed correctly."
                           )

let rec extract_nums_rec s sums ns = 
    match s with 
        | Sum ([]) -> (sums, ns)
        | Sum (x :: xs) -> (
                            match x with 
                                | Num (n) -> extract_nums_rec (Sum (xs)) sums (ns @ [n])
                                | Var (y) -> extract_nums_rec (Sum (xs)) (sums @ [x]) ns
                                | Prod (p) -> extract_nums_rec (Sum (xs)) (sums @ [x]) ns
                                | _ -> failwith "[Invalid argument] part of constraint has form 'Sum (Sum (xs))'. This should not happen if it was parsed correctly."
                           )
        | _ -> failwith "[Invalid argument] extract_nums: this function should only be called with sums";;

let extract_nums s = extract_nums_rec s [] [];;

(* Transforms the constraint into one that has all variables on the left side *)
(* of the comparator and all constants on the right. This is a necessary preprocessing *)
(* step in order to transform the constraint into the input format of the simplex procedure *)
let rec transform_constraint cons =
    match cons with
        | (Sum (s), Var (x)) -> (
                                 match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (Sum (ss @ [Prod ([Num (-1); Var (x)])]), Num (List.fold_left (-) 0 ns))
                                )
        | (Var (x), Sum (s)) -> (
                                 match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Num (-1); Var (x)])]))
                                )
        | (Sum (s), Num (n)) -> (
                                 match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (Sum (ss), Num (List.fold_left (-) n ns))
                                )
        | (Num (n), Sum (s)) -> (
                                 match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (Num (List.fold_left (-) n ns), Sum (ss))
                                )
        | (Sum (s), Prod (p)) -> (
                                  match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (
                                                         match p with 
                                                            | [Var (x); Num (n)] -> (Sum (ss @ [Prod ([Var (x); Num (-1 * n)])]), Num (List.fold_left (-) 0 ns))
                                                            | [Num (n); Var (x)] -> (Sum (ss @ [Prod ([Num (-1 * n); Var (x)])]), Num (List.fold_left (-) 0 ns))
                                                            | _ -> failwith "[Invalid argument] transform_constraint"
                                                        )
                                 )
        | (Prod (p), Sum (s)) -> (
                                  match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (
                                                         match p with 
                                                            | [Var (x); Num (n)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Var (x); Num (-1 * n)])]))
                                                            | [Num (n); Var (x)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Num (-1 * n); Var (x)])]))
                                                            | _ -> failwith "[Invalid argument] transform_constraint"
                                                        )
                                 )
        | (Sum (s1), Sum (s2)) -> (
                                   match (extract_nums (Sum (s1))) with
                                    | (ss1, ns1) -> (
                                                           match (extract_nums (Sum (s2))) with
                                                            | (ss2, ns2) -> (Sum (ss1 @ (negate_sum_vars (Sum ss2))), Num (List.fold_left (-) (List.fold_left (+) 0 ns2) ns1))
                                                          )
                                  )
        | _ -> failwith "[Invalid argument] transform_constraint";;

let rec op_to_simplex_format operator varlist varcount = 
    match operator with
        | Var (x) -> (
                      match (is_in_varlist varlist x) with 
                        | -1 -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                        | m -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                     )
        | Num (n) -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))), varlist, varcount)
        | Sum (s) -> (
                      match s with
                       | [x] -> op_to_simplex_format x varlist varcount
                       | x :: xs -> (
                                     match (op_to_simplex_format x varlist varcount) with
                                        | (s_lp, newlist_s, newcount_s) -> (
                                                                        match (op_to_simplex_format (Sum (xs)) newlist_s newcount_s) with
                                                                            | (ss_lp, newlist, newcount) -> ((Simplex.plus_linear_poly s_lp ss_lp), newlist, newcount)
                                                                       )
                                    )
                       | [] -> failwith "[Invalid argument] op_to_simplex_format: empty list Sum ([])"
                     )
        | Prod ([Var (x); Num (n)]) -> (
                                        match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                                       )               
        | Prod ([Num (n); Var (x)]) -> (
                                        match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                                       )       
        | _ -> failwith "[Invalid argument] op_to_simplex_format";;

let rec to_simplex_format assignment varlist varcount = 
    match assignment with
        | Assignment ([]) -> []
        | Assignment ((c, v, d, dl) :: xs) -> 
                   (
                    match c with
                    | AuxVar (x) -> to_simplex_format (Assignment (xs)) varlist varcount
                    | Constraint (LessEq (l, r)) -> (
                                                     match (l, r) with 
                                                        | (Var (x), Num (n)) -> 
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1))
                                                                            | (-1, false) -> [Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1)) 
                                                                            | (m, true) -> [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) varlist varcount)
                                                                            | (m, false) -> [Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) varlist varcount)
                                                                           )
                                                        | (Num (n), Var (x)) ->
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> [Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1))
                                                                            | (-1, false) -> [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1)) 
                                                                            | (m, true) -> [Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) varlist varcount)
                                                                            | (m, false) -> [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) varlist varcount)
                                                                           )
                                                        | (Var (x), Var (y)) ->
                                                                            (
                                                                             match (is_in_varlist varlist x) with 
                                                                              | -1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 2)))))] @ (to_simplex_format (Assignment (xs))(varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2))
                                                                                        | (-1, false) -> [Simplex.GTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 2)))))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2))
                                                                                        | (m, true) -> [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1))
                                                                                        | (m, false) -> [Simplex.GTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1))
                                                                                      )   
                                                                              | m1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1))
                                                                                        | (-1, false) -> [Simplex.GTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1))
                                                                                        | (m2, true) -> [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m2))))] @ (to_simplex_format (Assignment (xs)) varlist varcount)
                                                                                        | (m2, false) -> [Simplex.GTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m2))))] @ (to_simplex_format (Assignment (xs)) varlist varcount)
                                                                                      ) 
                                                                            )
                                                        | (Sum (s), Var (x)) -> 
                                                                        ( 
                                                                         match (transform_constraint (Sum (s), Var (x))) with 
                                                                            | (sums, Num (n)) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Var (x), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint (Var (x), Sum (s))) with 
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Sum (s), Num (n)) ->
                                                                        ( 
                                                                         match (transform_constraint (Sum (s), Num (n))) with 
                                                                            | (sums, Num (m)) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Num (n), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint (Num (n), Sum (s))) with 
                                                                            | (Num (m), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p), Var (x)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> [Simplex.LEQPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (-1, false) -> [Simplex.GTPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (m, true) -> [Simplex.LEQPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                        | (m, false) -> [Simplex.GTPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                    )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> [Simplex.GTPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (-1, false) -> [Simplex.LEQPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (m, true) -> [Simplex.GTPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                        | (m, false) -> [Simplex.LEQPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                    )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)   
                                                                                                                | false -> [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)            
                                                                                                               )        
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)   
                                                                                                                | false -> [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)            
                                                                                                               )  
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                        ( 
                                                                         match (transform_constraint (Sum (s), Prod (p))) with 
                                                                            | (sums, Num (n)) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint (Prod (p), Sum (s))) with 
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )   
                                                        | (Sum (s1), Sum (s2)) ->
                                                                        ( 
                                                                         match (transform_constraint (Sum (s1), Sum (s2))) with 
                                                                            | (sums, Num (n)) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                | false -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p1), Prod (p2)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p1)) varlist varcount) with
                                                                                | (p1_lp, newlist_p1, newcount_p1) -> 
                                                                                    (
                                                                                     match (op_to_simplex_format (Prod (p2)) newlist_p1 newcount_p1) with
                                                                                        | (p2_lp, newlist, newcount) -> (
                                                                                                                         match v with
                                                                                                                            | true -> [Simplex.LEQPP (p1_lp, p2_lp)] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                            | false -> [Simplex.GTPP (p1_lp, p2_lp)] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                                        )
                                                                                    )
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> (
                                                                                   match (compare n1 n2) with
                                                                                    | 1 -> (
                                                                                            match v with   
                                                                                            | true -> [Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)))] @ to_simplex_format (Assignment (xs)) varlist varcount
                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount
                                                                                           )
                                                                                    | _ -> (
                                                                                            match v with 
                                                                                             | true -> to_simplex_format (Assignment (xs)) varlist varcount
                                                                                             | false -> [Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)))] @ to_simplex_format (Assignment (xs)) varlist varcount
                                                                                           )
                                                                                  )
                                                    )
                   );;

let to_simplex_format_init assignment = to_simplex_format assignment [] 0;;