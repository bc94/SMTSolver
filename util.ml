open Types
open Simplex
open Simplex_inc
open Big_int

(* Print execution time of function 'f' applied to argument 'x' *)

let time f x =
    let start = Unix.gettimeofday ()
    in let res = f x
    in let stop = Unix.gettimeofday ()
    in let () = Printf.printf "%f\n%!" (stop -. start)
    in
       res;;

let add_if_is_mem xs x = if (List.mem x xs)
                         then xs 
                         else (xs @ [x]);;

let remove_duplicates xs = List.fold_left add_if_is_mem [] xs;;

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

let negate_prod prod =
    match prod with 
        | Prod ([Var (x); Num (n)]) -> Prod ([Var (x); Num (-1 * n)])
        | Prod ([Num (n); Var (x)]) -> Prod ([Num (-1 * n); Var (x)])
        | Prod ([Var (x); Div (Num (n1), Num (n2))]) -> Prod ([Var (x); Div (Num (-1 * n1), Num (n2))]) 
        | Prod ([Div (Num (n1), Num (n2)); Var (x)]) ->  Prod ([Div (Num (-1 * n1), Num (n2)); Var (x)])
        | _ -> failwith "[Invalid argument] negate_prod: argument not a product between var and num";;

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

let rec extract_nums_p_rec s sums ns = 
    match s with 
        | Sum ([]) -> (sums, ns)
        | Sum (x :: xs) -> (
                            match x with 
                                | Num (n) -> extract_nums_p_rec (Sum (xs)) sums (ns @ [n])
                                | Var (y) -> extract_nums_p_rec (Sum (xs)) (sums @ [x]) ns
                                | Prod (p) -> extract_nums_p_rec (Sum (xs)) (sums @ [(negate_prod x)]) ns
                                | _ -> failwith "[Invalid argument] part of constraint has form 'Sum (Sum (xs))'. This should not happen if it was parsed correctly."
                           )
        | _ -> failwith "[Invalid argument] extract_nums: this function should only be called with sums";;

let extract_nums_p s = extract_nums_p_rec s [] [];;

let rec sum_to_simplex_format_inc sum result = 
    match sum with
        | Sum ([]) -> result
        | Sum (x :: xs) -> (
                            match x with
                                | Num (n) -> sum_to_simplex_format_inc (Sum (xs)) (result + n)
                                | Sum (s) -> sum_to_simplex_format_inc (Sum (xs)) (result + sum_to_simplex_format_inc x 0)
                                | Var (x) -> failwith "[Invalid argument] sum_to_simplex_format_inc: constraint not linear"
                                | Prod (p) -> failwith "[Invalid argument] sum_to_simplex_format_inc: constraint not linear"
                           );;

let rec prod_to_simplex_format_inc prod =
    match prod with
        | Prod ([Var (x); Num (n)]) -> (x, n)
        | Prod ([Num (n); Var (x)]) -> (x, n)
        | Prod ([Prod (p); Num (n)]) -> let (x, m) = prod_to_simplex_format_inc (Prod (p)) in (x, n*m)
        | Prod ([Num (n); Prod (p)]) -> let (x, m) = prod_to_simplex_format_inc (Prod (p)) in (x, n*m)
        | Prod ([Prod (p); Sum (s)]) -> let (x, m) = prod_to_simplex_format_inc (Prod (p)) in
                                         let n = sum_to_simplex_format_inc (Sum (s)) 0 in (x, n*m)
        | Prod ([Sum (s); Prod (p)]) -> let (x, m) = prod_to_simplex_format_inc (Prod (p)) in
                                         let n = sum_to_simplex_format_inc (Sum (s)) 0 in (x, n*m)
        | Prod ([Prod (p); Var (x)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | Prod ([Var (x); Prod (p)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | Prod ([Prod (p1); Prod (p2)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | Prod ([Var (_); Var (_)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: argument not a product";;

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
                                 match (extract_nums_p (Sum (s))) with
                                    | (ss, ns) -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Var (x)]))
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
                                                            | [Var (x); Div (Num (n1), Num (n2))] -> (Sum (ss @ [Prod ([Var (x); Div (Num (-1 * n1), Num (n2))])]), Num (List.fold_left (-) 0 ns))
                                                            | [Div (Num (n1), Num (n2)); Var (x)] -> (Sum (ss @ [Prod ([Div (Num (-1 * n1), Num (n2)); Var (x)])]), Num (List.fold_left (-) 0 ns))
                                                            | _ -> failwith "[Invalid argument] transform_constraint"
                                                        )
                                 )
        | (Prod (p), Sum (s)) -> (
                                  match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (
                                                         match p with 
                                                            | [Var (x); Num (n)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Var (x); Num (-1 * n)])]))
                                                            | [Num (n); Var (x)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Num (-1 * n); Var (x)])]))
                                                            | [Var (x); Div (Num (n1), Num (n2))] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Var (x); Div (Num (-1 * n1), Num (n2))])]))
                                                            | [Div (Num (n1), Num (n2)); Var (x)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Div (Num (-1 * n1), Num (n2)); Var (x)])]))
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

let transform_constraint_var_sum_geq cons =
    match cons with
        | (Var (x), Sum (s)) -> (
                                 match (extract_nums (Sum (s))) with
                                    | (ss, ns) -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Num (-1); Var (x)])]))
                                )
        | _ -> failwith "[Invalid argument] transform_constraint_var_sum_geq: argument not a 'Var OPERATOR Sum' constraint";;

let transform_constraint_p cons =
    match cons with
        | (Prod (p), Sum (s)) -> (
                                  match (extract_nums_p (Sum (s))) with
                                    | (ss, ns) -> (
                                                         match p with 
                                                            | [Var (x); Num (n)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Var (x); Num (n)])]))
                                                            | [Num (n); Var (x)] -> (Num (List.fold_left (-) 0 ns), Sum (ss @ [Prod ([Num (n); Var (x)])]))
                                                            | _ -> failwith "[Invalid argument] transform_constraint"
                                                        )
                                 )
        | _ -> failwith "[Invalid argument] transform_constraint_p: constraint not a 'Product OPERATOR Product' constraint";;

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
        | Prod ([Var (_); Var (_)]) -> failwith "[Invalid argument] op_to_simplex_format: constraint not linear"
        | Prod ([p1; p2]) -> let (x, n) = prod_to_simplex_format_inc operator in
                                (
                                 match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), varlist, varcount)   
                                )
        | _ -> failwith "[Invalid argument] op_to_simplex_format";;


(* NOTE: x <= 1 negated must be x >= 2 and not x >= 1 *)
let rec to_simplex_format assignment varlist varcount result cs = 
    match assignment with
        | Assignment ([]) -> (result, Assignment (cs))
        | Assignment ((c, v, d, dl) :: xs) -> 
                   (
                    match c with
                    | AuxVar (x) -> to_simplex_format (Assignment (xs)) varlist varcount result cs
                    | Constraint (LessEq (l, r)) -> (
                                                     match (l, r) with 
                                                        | (Var (x), Num (n)) -> 
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) 
                                                                                                                                                                               (cs @ [(c, v, d, dl)])                        
                                                                            | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)])                  
                                                                            | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))])
                                                                                                                                                (cs @ [(c, v, d, dl)])       
                                                                            | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])  
                                                                           )
                                                        | (Num (n), Var (x)) ->
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                      (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)]) 
                                                                            | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))),
                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) 
                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                            | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                       (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))])
                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                            | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                         (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                           )
                                                        | (Var (x), Var (y)) ->
                                                                            (
                                                                             match (is_in_varlist varlist x) with 
                                                                              | -1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 2)))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                        | (_, false) -> ( 
                                                                                                          match (transform_constraint  (Var (x), Sum ([(Prod([(Num (1)); (Var (y))])); (Num (-1))]))) with 
                                                                                                                | (Num (n), sums) -> (
                                                                                                                                      match (op_to_simplex_format sums varlist varcount) with
                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                            to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                         )
                                                                                        | (m, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                      )   
                                                                              | m1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                                                     (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                        | (_, false) -> ( 
                                                                                                          match (transform_constraint (Var (x), Sum ([(Prod([(Num (1)); (Var (y))])); (Num (-1))]))) with 
                                                                                                                | (Num (n), sums) -> (
                                                                                                                                      match (op_to_simplex_format sums varlist varcount) with
                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                            to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                         )
                                                                                        | (m2, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                       (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m2))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
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
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Var (x), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_var_sum_geq (Var (x), Sum (s))) with 
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
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
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m + 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
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
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m - 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p), Var (x)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1) (result @ [Simplex.LEQPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))])
                                                                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                                        | (_, false) -> ( 
                                                                                                                        match (transform_constraint (Prod (p), Sum ([(Var (x)); (Num (-1))]))) with 
                                                                                                                                | (Num (n), sums) -> (
                                                                                                                                                    match (op_to_simplex_format sums varlist varcount) with
                                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                                            to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                    )
                                                                                                                        )      
                                                                                                        | (m, true) -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQPP (p_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))]) (cs @ [(c, v, d, dl)])
                                                                                                    )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1) (result @ [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))), p_lp)])
                                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                        | (_, false) -> ( 
                                                                                                                        match (transform_constraint (Var (x), Sum ([(Prod (p)); (Num (-1))]))) with 
                                                                                                                                | (Num (n), sums) -> (
                                                                                                                                                    match (op_to_simplex_format sums varlist varcount) with
                                                                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                                                            to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                    )
                                                                                                                        )  
                                                                                                        | (m, true) -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), p_lp)]) (cs @ [(c, v, d, dl)]) 
                                                                                                    )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])   
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])            
                                                                                                               )        
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])         
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
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
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
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
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
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p1), Prod (p2)) ->
                                                                           (
                                                                            match v with 
                                                                             | true -> (
                                                                                        match (op_to_simplex_format (Prod (p1)) varlist varcount) with
                                                                                         | (p1_lp, newlist_p1, newcount_p1) -> 
                                                                                                (
                                                                                                 match (op_to_simplex_format (Prod (p2)) newlist_p1 newcount_p1) with
                                                                                                    | (p2_lp, newlist, newcount) -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQPP (p1_lp, p2_lp)]) (cs @ [(c, v, d, dl)])
                                                                                                )
                                                                                       )
                                                                             | false -> ( 
                                                                                         match (transform_constraint_p (Prod (p1), Sum ([(Prod (p2)); (Num (-1))]))) with 
                                                                                            | (Num (n), sums) -> (
                                                                                                                  match (op_to_simplex_format sums varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                        to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                 )
                                                                                        )  
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> (
                                                                                   match (compare n1 n2) with
                                                                                    | 1 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                           )
                                                                                    | _ -> (
                                                                                            match v with 
                                                                                             | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                             | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                      Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])      
                                                                                           )
                                                                                  )
                                                    )
                   );;

let to_simplex_format_init assignment = to_simplex_format assignment [] 0 [] [];;

(******************************************************************)
(* Incremental simplex version of the format conversion functions *)
(******************************************************************)

let rec op_to_simplex_format_inc operator varlist varcount = 
    match operator with
        | Var (x) -> (
                      match (is_in_varlist varlist x) with 
                        | -1 -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                        | m -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                     )
        | Num (n) -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))), varlist, varcount)
        | Div (d1, d2) -> (
                           match (d1, d2) with 
                                | (Num (n1), Num (n2)) -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex_inc.nat_of_integer (big_int_of_int 0))), varlist, varcount)
                                | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: divison of non-num_type"
                          )
        | Sum (s) -> (
                      match s with
                       | [x] -> op_to_simplex_format_inc x varlist varcount
                       | x :: xs -> (
                                     match (op_to_simplex_format_inc x varlist varcount) with
                                        | (s_lp, newlist_s, newcount_s) -> (
                                                                        match (op_to_simplex_format_inc (Sum (xs)) newlist_s newcount_s) with
                                                                            | (ss_lp, newlist, newcount) -> ((Simplex_inc.plus_linear_poly s_lp ss_lp), newlist, newcount)
                                                                       )
                                    )
                       | [] -> failwith "[Invalid argument] op_to_simplex_format_inc: empty list Sum ([])"
                     )
        | Prod ([Var (x); Num (n)]) -> (
                                        match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                                       )               
        | Prod ([Num (n); Var (x)]) -> (
                                        match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                                       )       
        | Prod ([Var (x); Div (d1, d2)]) -> (
                                            match (d1, d2) with
                                                | (Num (n1), Num (n2)) -> (
                                                                            match (is_in_varlist varlist x) with 
                                                                            | -1 -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                            | m -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex_inc.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                                                                        ) 
                                                | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: division of non-num_type"
                                            )
        | Prod ([Div (d1, d2); Var (x)]) -> (
                                            match (d1, d2) with
                                                | (Num (n1), Num (n2)) -> (
                                                                            match (is_in_varlist varlist x) with 
                                                                            | -1 -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                            | m -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex_inc.nat_of_integer (big_int_of_int m))), varlist, varcount) 
                                                                        ) 
                                                | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: division of non-num_type"
                                            )
        | Prod ([Var (_); Var (_)]) -> failwith "[Invalid argument] op_to_simplex_format_inc: constraint not linear"
        | Prod ([p1; p2]) -> let (x, n) = prod_to_simplex_format_inc operator in
                                (
                                 match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), varlist, varcount)   
                                )
        | _ -> failwith "[Invalid argument] op_to_simplex_format_inc";;

let rec to_simplex_format_inc assignment varlist varcount result cs i_map = 
    match assignment with
        | Assignment ([]) -> (result, Assignment (cs))
        | Assignment ((c, v, d, dl) :: xs) -> 
                   (
                    match c with
                    | AuxVar (x) -> to_simplex_format_inc (Assignment (xs)) varlist varcount result cs i_map
                    | Constraint (LessEq (l, r)) -> (
                                                     match (l, r) with 
                                                        | (Var (x), Num (n)) -> 
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) 
                                                                                                                                                                               (cs @ [(c, v, d, dl)])
                                                                                                                                                                               i_map                        
                                                                            | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex_inc.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)])    
                                                                                                                                                                               i_map              
                                                                            | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])       
                                                                                                                                                i_map
                                                                            | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])  
                                                                                                                                                 i_map
                                                                           )
                                                        | (Num (n), Var (x)) ->
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                      (Simplex_inc.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                               i_map
                                                                            | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))),
                                                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                                                i_map
                                                                            | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                       (Simplex_inc.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                i_map
                                                                            | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                         (Simplex_inc.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                 i_map
                                                                           )
                                                        | (Var (x), Var (y)) ->
                                                                             (
                                                                             match (is_in_varlist varlist x) with 
                                                                              | -1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                 i_map
                                                                                        | (_, false) -> ( 
                                                                                                         match (transform_constraint (Var (x), Sum ([(Prod([(Num (1)); (Var (y))])); (Num (-1))]))) with 
                                                                                                                | (Num (n), sums) -> (
                                                                                                                                      match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                            to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                     )
                                                                                                         )
                                                                                        | (m, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                          i_map
                                                                                      )   
                                                                              | m1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                                                     (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                           i_map
                                                                                        | (_, false) -> ( 
                                                                                                          match (transform_constraint (Var (x), Sum ([(Prod([(Num (1)); (Var (y))])); (Num (-1))]))) with 
                                                                                                                | (Num (n), sums) -> (
                                                                                                                                      match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                            to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                     )
                                                                                                         )
                                                                                        | (m2, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                       (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                                                                                             i_map
                                                                                      ) 
                                                                            )
                                                        | (Sum (s), Var (x)) -> 
                                                                        ( 
                                                                         match (transform_constraint (Sum (s), Var (x))) with 
                                                                            | (sums, Num (n)) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Var (x), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_var_sum_geq (Var (x), Sum (s))) with 
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Sum (s), Num (n)) ->
                                                                        ( 
                                                                         match (transform_constraint (Sum (s), Num (n))) with 
                                                                            | (sums, Num (m)) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (m + 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Num (n), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint (Num (n), Sum (s))) with 
                                                                            | (Num (m), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (m - 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p), Var (x)) ->
                                                                           (
                                                                            match (op_to_simplex_format_inc (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP (p_lp, (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (newcount + 1))))))])
                                                                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                           i_map
                                                                                                        | (_, false) -> ( 
                                                                                                                        match (transform_constraint (Prod (p), Sum ([(Var (x)); (Num (-1))]))) with 
                                                                                                                                | (Num (n), sums) -> (
                                                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                                            to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                    )
                                                                                                                        )      
                                                                                                        | (m, true) -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP (p_lp, (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m)))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                    )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format_inc (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (newcount + 1)))), p_lp))])
                                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                                           i_map
                                                                                                        | (_, false) -> ( 
                                                                                                                        match (transform_constraint (Var (x), Sum ([(Prod (p)); (Num (-1))]))) with 
                                                                                                                                | (Num (n), sums) -> (
                                                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                                                            to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                    )
                                                                                                                        )  
                                                                                                        | (m, true) -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), p_lp))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                    )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (op_to_simplex_format_inc (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map  
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map            
                                                                                                               )        
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format_inc (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map  
                                                                                                               )  
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                        ( 
                                                                         match (transform_constraint (Sum (s), Prod (p))) with 
                                                                            | (sums, Num (n)) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint (Prod (p), Sum (s))) with 
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n - 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )   
                                                        | (Div (d1, d2), Var (x)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                               match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                i_map
                                                                                                                | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))),
                                                                                                                                                                                                            (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 - n2)) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                                                    i_map
                                                                                                                | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                    i_map
                                                                                                                | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                            (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 - n2)) (big_int_of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                    i_map
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Var (x), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) 
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                i_map                        
                                                                                                                | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 + n2)) (big_int_of_int n2))))])
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])    
                                                                                                                                                                                                                i_map              
                                                                                                                | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                                                            (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])       
                                                                                                                                                                                    i_map
                                                                                                                | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ ((Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                                                            (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 + n2)) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])  
                                                                                                                                                                                    i_map
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Div (d1, d2), Num (n)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match (compare ((float_of_int n1) /. (float_of_int n2)) (float_of_int n)) with
                                                                                                                    | 1 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                            i_map
                                                                                                                           )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Num (n), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match (compare (float_of_int n) ((float_of_int n1) /. (float_of_int n2))) with
                                                                                                                    | 1 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                            i_map
                                                                                                                           )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> ( 
                                                                                                               match (transform_constraint (Sum (s), Num (0))) with 
                                                                                                                | (sums, Num (m)) -> (
                                                                                                                                      match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                                                    (
                                                                                                                                                        match v with 
                                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 + (m * n2))) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 + n2 + (m * n2))) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                    )
                                                                                                                                     )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Div (d1, d2), Sum (s)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> ( 
                                                                                                                match (transform_constraint (Num (0), Sum (s))) with 
                                                                                                                    | (Num (m), sums) -> (
                                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                                    (
                                                                                                                                                        match v with 
                                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 + (m * n2))) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int ((n1 - n2) + (m * n2))) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                    )
                                                                                                                                        )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Prod (p), Div (d1, d2)) -> (
                                                                                    match (d1, d2) with 
                                                                                        | (Num (n1), Num (n2)) -> (
                                                                                                                    match (op_to_simplex_format_inc (Prod (p)) varlist varcount) with
                                                                                                                        | (p_lp, newlist, newcount) -> (
                                                                                                                                                        match v with 
                                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map  
                                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 + n2)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map            
                                                                                                                                                    )        
                                                                                                                  )
                                                                                        | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                   )
                                                        | (Div (d1, d2), Prod (p)) -> (
                                                                                    match (d1, d2) with 
                                                                                        | (Num (n1), Num (n2)) -> (
                                                                                                                    match (op_to_simplex_format_inc (Prod (p)) varlist varcount) with
                                                                                                                        | (p_lp, newlist, newcount) -> (
                                                                                                                                                        match v with 
                                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n1 - n2)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map  
                                                                                                                                                    )  
                                                                                                                  )
                                                                                        | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                   )
                                                        | (Div (d11, d12), Div (d21, d22)) -> (
                                                                                   match ((d11, d12), (d21, d22)) with 
                                                                                    | ((Num (n1d1), Num (n2d1)), (Num (n1d2), Num (n2d2))) -> (
                                                                                                    match (compare ((float_of_int n1d1) /. (float_of_int n2d1)) ((float_of_int n1d2) /. (float_of_int n2d2))) with
                                                                                                        | 1 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                                                                            i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                            )
                                                                                                        | _ -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                i_map
                                                                                                            )
                                                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s1), Sum (s2)) ->
                                                                        ( 
                                                                         match (transform_constraint (Sum (s1), Sum (s2))) with 
                                                                            | (sums, Num (n)) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (s_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int (n + 1)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                        )
                                                        | (Prod (p1), Prod (p2)) ->
                                                                           (
                                                                            match v with 
                                                                             | true -> (
                                                                                        match (op_to_simplex_format_inc (Prod (p1)) varlist varcount) with
                                                                                         | (p1_lp, newlist_p1, newcount_p1) -> 
                                                                                                (
                                                                                                 match (op_to_simplex_format_inc (Prod (p2)) newlist_p1 newcount_p1) with
                                                                                                    | (p2_lp, newlist, newcount) -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.LEQPP (p1_lp, p2_lp))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                )
                                                                                       )
                                                                             | false -> ( 
                                                                                         match (transform_constraint_p (Prod (p1), Sum ([(Prod (p2)); (Num (-1))]))) with 
                                                                                            | (Num (n), sums) -> (
                                                                                                                  match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                        to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GEQ (p_lp, (Simplex_inc.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                 )
                                                                                        )  
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> (
                                                                                   match (compare n1 n2) with
                                                                                    | 1 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find (Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                    Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                                                                                           i_map
                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                           )
                                                                                    | _ -> (
                                                                                            match v with 
                                                                                             | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                             | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_inc.nat_of_integer (big_int_of_int (Tseitin.Index_Map.find ("-" ^ Printing.print_constraint_n c) i_map)), Simplex_inc.GTPP (Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                      Simplex_inc.lp_monom (Simplex_inc.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex_inc.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])      
                                                                                                                                                             i_map
                                                                                           )
                                                                                  )
                                                    )
                   );;

let to_simplex_format_inc_init assignment i_map = to_simplex_format_inc assignment [] 0 [] [] i_map;;

