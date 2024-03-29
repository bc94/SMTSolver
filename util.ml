open Types
open Simplex
open Simplex_inc
open Simplex_Inc
open Big_int
open Simplex_Validity_Checker

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

(* These functions were used for the indexed, incremental list based *)
(* DPLL implementation that was implemented temporarily to check viability *)
(* of this approach over two-watched literals. It proved inferior and therefore *)
(* is not used anymore. The DPLL implementation can be found commented out at the *)
(* end of the 'solver.ml' file *)

(*let rec construct_modifiable_formula_clause c =
    match c with 
        | Disjunction ([]) -> []
        | Disjunction (x :: xs) -> [x] @ (construct_modifiable_formula_clause (Disjunction (xs)));;

let rec construct_modifiable_formula_disj l = 
    match l with
     | [] -> []
     | x :: xs -> let ys = construct_modifiable_formula_clause x in [(ys, ys)] @ (construct_modifiable_formula_disj xs);;

let construct_modifiable_formula_conj f = 
    let Conjunction (xs) = f in construct_modifiable_formula_disj xs;;

let construct_modifiable_formula formula = 
    let Formula (f) = formula in construct_modifiable_formula_conj f;;*)

(************************************************************************************)

(* The following functions convert a formula of Types.formula type *)
(* to a type that is accepted by the exported CeTA SMT solver *)

let rec to_ceta_expr_l l =
    match l with
        | [] -> []
        | x :: xs -> [(to_ceta_expr x)] @ (to_ceta_expr_l xs)

and to_ceta_expr expr = 
    match expr with
        | Sum (xs) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.SumFa (Simplex_Validity_Checker.nat_of_integer (big_int_of_int (List.length xs))), to_ceta_expr_l xs)
        | Prod (xs) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.ProdFa (Simplex_Validity_Checker.nat_of_integer (big_int_of_int (List.length xs))), to_ceta_expr_l xs)
        | Num (x) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.ConstFa (Simplex_Validity_Checker.Frct (Simplex_Validity_Checker.Int_of_integer (big_int_of_int x), Simplex_Validity_Checker.Int_of_integer (big_int_of_int 1))), [])
        | Div (Num (x), Num (y)) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.ConstFa (Simplex_Validity_Checker.Frct (Simplex_Validity_Checker.Int_of_integer (big_int_of_int x), Simplex_Validity_Checker.Int_of_integer (big_int_of_int y))), [])
        | Var (x) -> Simplex_Validity_Checker.Var ((Simplex_Validity_Checker.explode x), Simplex_Validity_Checker.RatT)
        | _ -> failwith "[Invalid argument] to_ceta_expr";;

let to_ceta_constraint cons =
    match cons with
        | Constraint (LessEq (l, r)) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.LeFa, [(to_ceta_expr l)] @ [(to_ceta_expr r)])
        | Constraint (Less (l, r)) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.LessFa, [(to_ceta_expr l)] @ [(to_ceta_expr r)])
        | Constraint (Eq (l, r)) -> Simplex_Validity_Checker.Fun (Simplex_Validity_Checker.EqFa, [(to_ceta_expr l)] @ [(to_ceta_expr r)])
        | _ -> failwith "[Invalid argument] to_ceta_constraint";;

let rec to_ceta_format_l l = 
    match l with
        | [] -> []
        | x :: xs -> [(to_ceta_format_rec x)] @ (to_ceta_format_l xs)

and to_ceta_format_rec elem = 
    match elem with 
        | Not (x) ->  Simplex_Validity_Checker.FNegate (to_ceta_format_rec x)
        | Conjunction (xs) -> Simplex_Validity_Checker.FConjunction (to_ceta_format_l xs) 
        | Disjunction (xs) -> Simplex_Validity_Checker.FDisjunction (to_ceta_format_l xs) 
        | Atom (x) -> Simplex_Validity_Checker.FAtom (to_ceta_constraint x);;

let to_ceta_format f = 
    match f with 
     | Formula (x) -> to_ceta_format_rec x;;

(************************************************************************************)

(* Functions for variable substitution needed for dealing with the smt2 format *)

let rec substitute_num_type_l v l = 
    match l with
        | x :: xs -> [(substitute_num_type v x)] @ (substitute_num_type_l v xs) 
        | [] -> []

and substitute_num_type v nt = 
    match nt with 
        | Sum (x :: xs) -> Sum ([(substitute_num_type v x)] @ (substitute_num_type_l v xs))
        | Prod (x :: xs) -> Prod ([(substitute_num_type v x)] @ (substitute_num_type_l v xs))
        | Div (x, y) -> Div (x, y)
        | Num (n) -> Num (n)
        | Var (x) -> (
                      match v with 
                       | SubstElem (Var (var_name), replacement) -> Var (x)
                       | SubstNum (Var (var_name), replacement) -> (
                                                                    match (compare x var_name) with
                                                                    | 0 -> replacement
                                                                    | _ -> Var (x)
                                                                    )
                       | _ -> failwith "[Invalid argument] substitute_constraint: replacement not of substitution type element, constraint or num"
                     );;

let rec substitute_constraint v c = 
    match c with
        | Constraint (LessEq (l, r)) -> Constraint (LessEq ((substitute_num_type v l), (substitute_num_type v r)))
        | Constraint (Less (l, r)) -> Constraint (Less ((substitute_num_type v l), (substitute_num_type v r)))
        | Constraint (Eq (l, r)) -> Constraint (Eq ((substitute_num_type v l), (substitute_num_type v r)));;

let rec substitute_l v l =
    match l with 
        | x :: xs -> [(substitute v x)] @ (substitute_l v xs)
        | [] -> []

and substitute v form = 
    match form with 
        | Not (x) -> Not (substitute v x)
        | Conjunction (x :: xs) -> Conjunction ([(substitute v x)] @ (substitute_l v xs))
        | Disjunction (x :: xs) -> Disjunction ([(substitute v x)] @ (substitute_l v xs))
        | Atom (RVar (x)) -> (
                            match v with 
                            | SubstElem (Var (var_name), replacement) -> (
                                                                          match (compare x var_name) with
                                                                            | 0 -> replacement
                                                                            | _ -> Atom (RVar (x))
                                                                         )
                            | SubstNum (Var (var_name), replacement) -> Atom (RVar (x))
                            | _ -> failwith "[Invalid argument] substitute_constraint: replacement not of substitution type element, constraint or num"
                            )
        | Atom (x) -> Atom (substitute_constraint v x);;

let rec variable_substitution_rec f =
    match f with 
        | (x :: xs, formula) -> let Formula (form) = formula  in (variable_substitution_rec (xs, Formula (substitute x form)))
        | ([], formula) -> formula
        | _ -> failwith "[Invalid argument] variable_substitution";;

let variable_substitution f =
    match f with 
        | (Some (x :: xs), formula) -> let Formula (form) = formula  in (variable_substitution_rec (xs, Formula (substitute x form)))
        | (Some ([]), formula) -> formula
        | _ -> failwith "[Invalid argument] variable_substitution";;

(************************************************************************************)

(* The following functions are all functions used for transforming arithmetic expressions *)
(* to a form that can be directly converted to the simplex constraint types. Some of them *)
(* are older versions of functions that have been replaced by new, more expansive ones, when *)
(* the smt2 format was introduced. *)

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
        | Prod ([x; Num (n)]) -> Prod ([x; Num (-1 * n)])
        | Prod ([Num (n); x]) -> Prod ([Num (-1 * n); x])
        | Prod ([x; Div (Num (n1), Num (n2))]) -> Prod ([x; Div (Num (-1 * n1), Num (n2))]) 
        | Prod ([Div (Num (n1), Num (n2)); x]) ->  Prod ([Div (Num (-1 * n1), Num (n2)); x])
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

let rec multiply_sum s num =
    match s with 
     | Sum ([]) -> []
     | Sum (x :: xs) -> (
                         match (x, num) with 
                          | (Num (n), Num (m)) -> [Num (n*m)] @ (multiply_sum (Sum (xs)) num)
                          | (Num (n), Div (Num (m1), Num(m2))) -> [Div (Num (n*m1), Num (m2))] @ (multiply_sum (Sum (xs)) num)
                          | (Div (Num (n1), Num (n2)), Num (m)) -> [Div (Num (m*n1), Num (n2))] @ (multiply_sum (Sum (xs)) num)
                          | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> [Div (Num (n1*m1), Num (n2*m2))] @ (multiply_sum (Sum (xs)) num)
                          | (_, _) -> [Prod ([x; num])] @ (multiply_sum (Sum (xs)) num)
                        );;

let rec prod_to_simplex_format_inc prod =
    match prod with
        | Prod ([Var (x); Num (n)]) -> (Var (x), Num (n))
        | Prod ([Num (n); Var (x)]) -> (Var (x), Num (n))
        | Prod ([Var (x); Div (Num (n1), Num (n2))]) -> (Var (x), Div (Num (n1), Num (n2)))
        | Prod ([Div (Num (n1), Num (n2)); Var (x)]) -> (Var (x), Div (Num (n1), Num (n2)))
        | Prod ([Prod (p); Num (n)]) -> (
                                         match prod_to_simplex_format_inc (Prod (p)) with 
                                          | (x, Num (m)) -> (x, Num (n*m))
                                          | (x, Div (Num (m1), Num (m2))) -> (x, Div (Num (n*m1), Num (m2)))
                                          | (Sum (s), _) -> let s_new = Sum (multiply_sum (Sum (s)) (Num (n))) in (s_new, s_new)
                                          | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: returned value not a Num or Div"
                                        )
        | Prod ([Num (n); Prod (p)]) -> (
                                         match prod_to_simplex_format_inc (Prod (p)) with 
                                          | (x, Num (m)) -> (x, Num (n*m))
                                          | (x, Div (Num (m1), Num (m2))) -> (x, Div (Num (n*m1), Num (m2)))
                                          | (Sum (s), _) -> let s_new = Sum (multiply_sum (Sum (s)) (Num (n))) in (s_new, s_new)
                                          | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: returned value not a Num or Div"
                                        )
        | Prod ([Prod (p); Sum (s)]) -> let n = sum_to_simplex_format_inc (Sum (s)) 0 in 
                                         (
                                         match prod_to_simplex_format_inc (Prod (p)) with 
                                          | (x, Num (m)) -> (x, Num (n*m))
                                          | (x, Div (Num (m1), Num (m2))) -> (x, Div (Num (n*m1), Num (m2)))
                                          | (Sum (s), _) -> let s_new = Sum (multiply_sum (Sum (s)) (Num (n))) in (s_new, s_new)
                                          | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: returned value not a Num or Div"
                                        )
        | Prod ([Sum (s); Prod (p)]) -> let n = sum_to_simplex_format_inc (Sum (s)) 0 in 
                                         (
                                         match prod_to_simplex_format_inc (Prod (p)) with 
                                          | (x, Num (m)) -> (x, Num (n*m))
                                          | (x, Div (Num (m1), Num (m2))) -> (x, Div (Num (n*m1), Num (m2)))
                                          | (Sum (s), _) -> let s_new = Sum (multiply_sum (Sum (s)) (Num (n))) in (s_new, s_new)
                                          | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: returned value not a Num or Div"
                                        )
        | Prod ([Sum (s); Num (n)]) -> let s_new = Sum (multiply_sum (Sum (s)) (Num (n))) in (s_new, s_new)
        | Prod ([Num (n); Sum (s)]) -> let s_new = Sum (multiply_sum (Sum (s)) (Num (n))) in (s_new, s_new)
        | Prod ([Sum (s); Div (Num (n1), Num (n2))]) -> let s_new = Sum (multiply_sum (Sum (s)) (Div (Num (n1), Num (n2)))) in (s_new, s_new)
        | Prod ([Div (Num (n1), Num (n2)); Sum (s)]) -> let s_new = Sum (multiply_sum (Sum (s)) (Div (Num (n1), Num (n2)))) in (s_new, s_new)
        | Prod ([Prod (p); Div (Num (n1), Num (n2))]) -> (
                                                          match prod_to_simplex_format_inc (Prod (p)) with 
                                                           | (x, Num (m)) -> (x, Div (Num (m*n1), Num (n2)))
                                                           | (x, Div (Num (m1), Num (m2))) -> (x, Div (Num (n1*m1), Num (n2*m2)))
                                                           | (Sum (s), _) -> let s_new = Sum (multiply_sum (Sum (s)) (Div (Num (n1), Num (n2)))) in (s_new, s_new)
                                                           | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: returned value not a Num or Div"
                                                         )
        | Prod ([Div (Num (n1), Num (n2)); Prod (p)]) -> (
                                                          match prod_to_simplex_format_inc (Prod (p)) with 
                                                           | (x, Num (m)) -> (x, Div (Num (m*n1), Num (n2)))
                                                           | (x, Div (Num (m1), Num (m2))) -> (x, Div (Num (n1*m1), Num (n2*m2)))
                                                           | (Sum (s), _) -> let s_new = Sum (multiply_sum (Sum (s)) (Div (Num (n1), Num (n2)))) in (s_new, s_new)
                                                           | _ -> failwith "[Invalid argument] prod_to_simplex_format_inc: returned value not a Num or Div"
                                                         )
        | Prod ([Prod (p); Var (x)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | Prod ([Var (x); Prod (p)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | Prod ([Prod (p1); Prod (p2)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | Prod ([Var (_); Var (_)]) -> failwith "[Invalid argument] prod_to_simplex_format_inc: constraint not linear"
        | _ -> Printf.printf "%s\n" (Printing.print_num_type prod); failwith "[Invalid argument] prod_to_simplex_format_inc: argument not a product";;

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

let rec sum_transformed_constraints sumlist vars constant =
    match sumlist with 
        | [] -> (
                 match vars with 
                 | [] -> (None, constant)
                 | xs -> (Some (Sum (vars)), constant)
                )
        | x :: xs -> (
                      match transform_constraint_smt2_rec x None None with 
                        | (Some (y), Some (Num (n))) -> (
                                                        match constant with 
                                                        | Some (Num (m)) -> sum_transformed_constraints xs (vars @ [y]) (Some (Num (n+m)))
                                                        | Some (Div (Num (m1), Num (m2))) -> sum_transformed_constraints xs (vars @ [y]) (Some (Div (Num (m1+(n*m2)), Num (m2))))
                                                        | None -> sum_transformed_constraints xs (vars @ [y]) (Some (Num (n)))
                                                        )
                        | (None, Some (Num (n))) -> (
                                                     match constant with 
                                                        | Some (Num (m)) -> sum_transformed_constraints xs vars (Some (Num (n+m)))
                                                        | Some (Div (Num (m1), Num (m2))) -> sum_transformed_constraints xs vars (Some (Div (Num (m1+(n*m2)), Num (m2))))
                                                        | None -> sum_transformed_constraints xs vars (Some (Num (n)))
                                                    )
                        | (Some (y), Some (Div (Num (n1), Num (n2)))) -> (
                                                                          match constant with 
                                                                           | Some (Num (m)) -> sum_transformed_constraints xs (vars @ [y]) (Some (Div (Num (n1+(m*n2)), Num (n2))))
                                                                           | Some (Div (Num (m1), Num (m2))) -> sum_transformed_constraints xs (vars @ [y]) (Some (Div (Num ((m1*n2)+(n1*m2)), Num (n2*m2))))
                                                                           | None -> sum_transformed_constraints xs (vars @ [y]) (Some (Div (Num (n1), Num (n2))))
                                                                         )
                        | (None, Some (Div (Num (n1), Num (n2)))) -> (
                                                                     match constant with 
                                                                           | Some (Num (m)) -> sum_transformed_constraints xs vars (Some (Div (Num (n1+(m*n2)), Num (n2))))
                                                                           | Some (Div (Num (m1), Num (m2))) -> sum_transformed_constraints xs vars (Some (Div (Num ((m1*n2)+(n1*m2)), Num (n2*m2))))
                                                                           | None -> sum_transformed_constraints xs vars (Some (Div (Num (n1), Num (n2))))
                                                                    )
                        | (Some (y), None) -> sum_transformed_constraints xs (vars @ [y]) constant
                        | (None, None) -> failwith "[Invalid argument] sum_transformed_constraints: one of the elements of the sum contains neither variables nor constants"
                     )

and transform_constraint_smt2_rec expr vars constant = 
    match expr with 
        | Var (x) -> (Some (expr), constant)
        | Num (n) -> (vars, Some (expr))
        | Div (x, y) -> (vars, Some (expr))
        | Sum (xs) -> sum_transformed_constraints xs [] None
        | Prod (xs) -> (
                        match xs with 
                         | [Var (x); Num (n)] -> (Some (expr), constant)
                         | [Var (x); Div (n1, n2)] -> (Some (expr), constant)
                         | [Num (n); Var (x)] -> (Some (expr), constant)
                         | [Div (n1, n2); Var (x)] -> (Some (expr), constant)
                         | [x; Num (n)] -> (
                                            match transform_constraint_smt2_rec x None None with 
                                             | (Some (y), Some (Num (m))) -> (Some (Prod ([y; Num (n)])), Some (Num (n*m)))
                                             | (Some (y), Some (Div (Num (m1), Num (m2)))) -> (Some (Prod ([y; Num (n)])), Some (Div (Num (n*m1), Num (m2))))
                                             | (Some (y), None) -> (Some (expr), None)
                                             | (None, Some (Num (m))) -> (None, Some (Num (n*m)))
                                             | (None, Some (Div (Num (m1), Num (m2)))) -> (None, Some (Div (Num (n*m1), Num (m2))))
                                             | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a product contains neither variables nor constants"
                                           )
                         | [x; Div (Num (n1), Num (n2))] -> (
                                                            match transform_constraint_smt2_rec x None None with 
                                                            | (Some (y), Some (Num (m))) -> (Some (Prod ([y; Div (Num (n1), Num (n2))])), Some (Div (Num (m*n1), Num (n2))))
                                                            | (Some (y), Some (Div (Num (m1), Num (m2)))) -> (Some (Prod ([y; Div (Num (n1), Num (n2))])), Some (Div (Num (n1*m1), Num (n2*m2))))
                                                            | (Some (y), None) -> (Some (expr), None)
                                                            | (None, Some (Num (m))) -> (None, Some (Div (Num (m*n1), Num (n2))))
                                                            | (None, Some (Div (Num (m1), Num (m2)))) -> (None, Some (Div (Num (n1*m1), Num (n2*m2))))
                                                            | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a product contains neither variables nor constants"
                                                            )
                         | [Num (n); x] -> (
                                            match transform_constraint_smt2_rec x None None with 
                                             | (Some (y), Some (Num (m))) -> (Some (Prod ([y; Num (n)])), Some (Num (n*m)))
                                             | (Some (y), Some (Div (Num (m1), Num (m2)))) -> (Some (Prod ([y; Num (n)])), Some (Div (Num (n*m1), Num (m2))))
                                             | (Some (y), None) -> (Some (expr), None)
                                             | (None, Some (Num (m))) -> (None, Some (Num (n*m)))
                                             | (None, Some (Div (Num (m1), Num (m2)))) -> (None, Some (Div (Num (n*m1), Num (m2))))
                                             | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a product contains neither variables nor constants"
                                           )
                         | [Div (Num (n1), Num (n2)); x] -> (
                                                            match transform_constraint_smt2_rec x None None with 
                                                            | (Some (y), Some (Num (m))) -> (Some (Prod ([y; Div (Num (n1), Num (n2))])), Some (Div (Num (m*n1), Num (n2))))
                                                            | (Some (y), Some (Div (Num (m1), Num (m2)))) -> (Some (Prod ([y; Div (Num (n1), Num (n2))])), Some (Div (Num (n1*m1), Num (n2*m2))))
                                                            | (Some (y), None) -> (Some (expr), None)
                                                            | (None, Some (Num (m))) -> (None, Some (Div (Num (m*n1), Num (n2))))
                                                            | (None, Some (Div (Num (m1), Num (m2)))) -> (None, Some (Div (Num (n1*m1), Num (n2*m2))))
                                                            | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a product contains neither variables nor constants"
                                                            )
                         | [Sum (s); Prod (p)] -> (
                                                   match p with 
                                                    | [Num (n); Num (m)] -> (
                                                                            match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                            | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Num (n*m)])), Some (Num (l*n*m)))
                                                                            | (Some (y), Some (Div (Num (m1), Num (m2)))) -> (Some (Prod ([y; Num (n*m)])), Some (Div (Num (n*m*m1), Num (m2))))
                                                                            | (Some (y), None) -> (Some (Prod ([Sum (s); Num (n*m)])), None)
                                                                            | (None, Some (Num (l))) -> (None, Some (Num (l*n*m)))
                                                                            | (None, Some (Div (Num (m1), Num (m2)))) -> (None, Some (Div (Num (n*m*m1), Num (m2))))
                                                                            | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                            )
                                                    | [Num (n); Div (Num (m1), Num (m2))] -> (
                                                                                             match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                                             | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Div (Num (n*m1), Num (m2))])), Some (Div (Num (l*n*m1), Num (m2))))
                                                                                             | (Some (y), Some (Div (Num (l1), Num (l2)))) -> (Some (Prod ([y; Div (Num (n*m1), Num (m2))])), Some (Div (Num (l1*n*m1), Num (l2*m2))))
                                                                                             | (Some (y), None) -> (Some (Prod ([Sum (s); Div (Num (n*m1), Num (m2))])), None)
                                                                                             | (None, Some (Num (l))) -> (None, Some (Div (Num (l*n*m1), Num (m2))))
                                                                                             | (None, Some (Div (Num (l1), Num (l2)))) -> (None, Some (Div (Num (l1*n*m1), Num (l2*m2))))
                                                                                             | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                                             )
                                                    | [Div (Num (n1), Num (n2)); Num (m)] -> (
                                                                                             match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                                             | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Div (Num (m*n1), Num (n2))])), Some (Div (Num (l*m*n1), Num (n2))))
                                                                                             | (Some (y), Some (Div (Num (l1), Num (l2)))) -> (Some (Prod ([y; Div (Num (m*n1), Num (n2))])), Some (Div (Num (l1*m*n1), Num (l2*n2))))
                                                                                             | (Some (y), None) -> (Some (Prod ([Sum (s); Div (Num (n1*m), Num (n2))])), None)
                                                                                             | (None, Some (Num (l))) -> (None, Some (Div (Num (l*m*n1), Num (n2))))
                                                                                             | (None, Some (Div (Num (l1), Num (l2)))) -> (None, Some (Div (Num (l1*m*n1), Num (l2*n2))))
                                                                                             | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                                             )
                                                    | [Div (Num (n1), Num (n2)); Div (Num (m1), Num (m2))] -> (
                                                                                                                match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                                                                | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Div (Num (m1*n1), Num (m2*n2))])), Some (Div (Num (l*m1*n1), Num (m2*n2))))
                                                                                                                | (Some (y), Some (Div (Num (l1), Num (l2)))) -> (Some (Prod ([y; Div (Num (m1*n1), Num (m2*n2))])), Some (Div (Num (l1*m1*n1), Num (l2*m2*n2))))
                                                                                                                | (Some (y), None) -> (Some (Prod ([Sum (s); Div (Num (n1*m1), Num (n2*m2))])), None)
                                                                                                                | (None, Some (Num (l))) -> (None, Some (Div (Num (l*m1*n1), Num (m2*n2))))
                                                                                                                | (None, Some (Div (Num (l1), Num (l2)))) -> (None, Some (Div (Num (l1*m1*n1), Num (l2*m2*n2))))
                                                                                                                | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                                                              )
                                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2_rec: unsupported arithmetic expression"
                                                  )
                         | [Prod (p); Sum (s)] -> (
                                                   match p with 
                                                    | [Num (n); Num (m)] -> (
                                                                            match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                            | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Num (n*m)])), Some (Num (l*n*m)))
                                                                            | (Some (y), Some (Div (Num (m1), Num (m2)))) -> (Some (Prod ([y; Num (n*m)])), Some (Div (Num (n*m*m1), Num (m2))))
                                                                            | (Some (y), None) -> (Some (Prod ([Sum (s); Num (n*m)])), None)
                                                                            | (None, Some (Num (l))) -> (None, Some (Num (l*n*m)))
                                                                            | (None, Some (Div (Num (m1), Num (m2)))) -> (None, Some (Div (Num (n*m*m1), Num (m2))))
                                                                            | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                            )
                                                    | [Num (n); Div (Num (m1), Num (m2))] -> (
                                                                                             match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                                             | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Div (Num (n*m1), Num (m2))])), Some (Div (Num (l*n*m1), Num (m2))))
                                                                                             | (Some (y), Some (Div (Num (l1), Num (l2)))) -> (Some (Prod ([y; Div (Num (n*m1), Num (m2))])), Some (Div (Num (l1*n*m1), Num (l2*m2))))
                                                                                             | (Some (y), None) -> (Some (Prod ([Sum (s); Div (Num (n*m1), Num (m2))])), None)
                                                                                             | (None, Some (Num (l))) -> (None, Some (Div (Num (l*n*m1), Num (m2))))
                                                                                             | (None, Some (Div (Num (l1), Num (l2)))) -> (None, Some (Div (Num (l1*n*m1), Num (l2*m2))))
                                                                                             | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                                             )
                                                    | [Div (Num (n1), Num (n2)); Num (m)] -> (
                                                                                             match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                                             | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Div (Num (m*n1), Num (n2))])), Some (Div (Num (l*m*n1), Num (n2))))
                                                                                             | (Some (y), Some (Div (Num (l1), Num (l2)))) -> (Some (Prod ([y; Div (Num (m*n1), Num (n2))])), Some (Div (Num (l1*m*n1), Num (l2*n2))))
                                                                                             | (Some (y), None) -> (Some (Prod ([Sum (s); Div (Num (n1*m), Num (n2))])), None)
                                                                                             | (None, Some (Num (l))) -> (None, Some (Div (Num (l*m*n1), Num (n2))))
                                                                                             | (None, Some (Div (Num (l1), Num (l2)))) -> (None, Some (Div (Num (l1*m*n1), Num (l2*n2))))
                                                                                             | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                                             )
                                                    | [Div (Num (n1), Num (n2)); Div (Num (m1), Num (m2))] -> (
                                                                                                                match transform_constraint_smt2_rec (Sum (s)) None None with 
                                                                                                                | (Some (y), Some (Num (l))) -> (Some (Prod ([y; Div (Num (m1*n1), Num (m2*n2))])), Some (Div (Num (l*m1*n1), Num (m2*n2))))
                                                                                                                | (Some (y), Some (Div (Num (l1), Num (l2)))) -> (Some (Prod ([y; Div (Num (m1*n1), Num (m2*n2))])), Some (Div (Num (l1*m1*n1), Num (l2*m2*n2))))
                                                                                                                | (Some (y), None) -> (Some (Prod ([Sum (s); Div (Num (n1*m1), Num (n2*m2))])), None)
                                                                                                                | (None, Some (Num (l))) -> (None, Some (Div (Num (l*m1*n1), Num (m2*n2))))
                                                                                                                | (None, Some (Div (Num (l1), Num (l2)))) -> (None, Some (Div (Num (l1*m1*n1), Num (l2*m2*n2))))
                                                                                                                | (None, None) -> failwith "[Invalid argument] transform_constraint_smt2_rec: one of the elements of a sum contains neither variables nor constants"
                                                                                                              )
                                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2_rec: unsupported arithmetic expression"
                                                  )
                         | _ -> failwith "[Invalid argument] transform_constraint_smt2_rec: unsupported arithmetic expression"
                       );;        

(* The new function for transforming constraints introduced with the smt2 format. *)
(* This one is used instead of the old variants now. *)
let transform_constraint_smt2 cons =
    match cons with
        | (Sum (s), Var (x)) -> (
                                 match (transform_constraint_smt2_rec (Sum (s)) None None) with
                                    | (Some (Sum (ss)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (n) -> (Sum (ss @ [Prod ([Num (-1); Var (x)])]), Num (0-n))
                                                                        | Div (Num (n1), Num (n2)) -> (Sum (ss @ [Prod ([Num (-1); Var (x)])]), Div (Num (0-n1), Num (n2)))
                                                                      )   
                                    | (Some (Sum (ss)), None) -> (Sum (ss @ [Prod ([Num (-1); Var (x)])]), Num (0))
                                    | (None, Some (ns)) -> (
                                                            match ns with 
                                                            | Num (n) -> (Prod ([Num (-1); Var (x)]), Num (0-n))
                                                            | Div (Num (n1), Num (n2)) -> (Prod ([Num (-1); Var (x)]), Div (Num (0-n1), Num (n2)))
                                                           )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Var (x), Sum (s)) -> (
                                 match (transform_constraint_smt2_rec (Sum (s)) None None) with
                                    | (Some (Sum (ss)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (n) -> (Num (0-n), Sum (ss @ [Prod ([Num (-1); Var (x)])]))
                                                                        | Div (Num (n1), Num (n2)) -> (Div (Num (0-n1), Num (n2)), Sum (ss @ [Prod ([Num (-1); Var (x)])]))
                                                                      )   
                                    | (Some (Sum (ss)), None) -> (Num (0), Sum (ss @ [Prod ([Num (-1); Var (x)])]))
                                    | (None, Some (ns)) -> (
                                                            match ns with 
                                                            | Num (n) -> (Num (0-n), Prod ([Num (-1); Var (x)]))
                                                            | Div (Num (n1), Num (n2)) -> (Div (Num (0-n1), Num (n2)), Prod ([Num (-1); Var (x)]))
                                                           )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Sum (s), Num (n)) -> (
                                 match (transform_constraint_smt2_rec (Sum (s)) None None) with
                                    | (Some (Sum (ss)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (m) -> (Sum (ss), Num (n-m))
                                                                        | Div (Num (m1), Num (m2)) -> (Sum (ss), Div (Num ((n*m2)-m1), Num (m2)))
                                                                      )   
                                    | (Some (Sum (ss)), None) -> (Sum (ss), Num (n))
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Num (n), Sum (s)) -> (
                                 match (transform_constraint_smt2_rec (Sum (s)) None None) with
                                    | (Some (Sum (ss)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (m) -> (Num (n-m), Sum (ss))
                                                                        | Div (Num (m1), Num (m2)) -> (Div (Num ((n*m2)-m1), Num (m2)), Sum (ss))
                                                                      )   
                                    | (Some (Sum (ss)), None) -> (Num (n), Sum (ss))
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Sum (s), Div (Num (n1), Num (n2))) -> (
                                                  match (transform_constraint_smt2_rec (Sum (s)) None None) with
                                                    | (Some (Sum (ss)), Some (ns)) -> (
                                                                                    match ns with 
                                                                                        | Num (m) -> (Sum (ss), Div (Num (n1-(m*n2)), Num (n2)))
                                                                                        | Div (Num (m1), Num (m2)) -> (Sum (ss), Div (Num ((n1*m2)-(m1*n2)), Num (m2*n2)))
                                                                                    )   
                                                    | (Some (Sum (ss)), None) -> (Sum (ss), Div (Num (n1), Num (n2)))
                                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                                 )
        | (Div (Num (n1), Num (n2)), Sum (s)) -> (
                                                  match (transform_constraint_smt2_rec (Sum (s)) None None) with
                                                    | (Some (Sum (ss)), Some (ns)) -> (
                                                                                    match ns with 
                                                                                        | Num (m) -> (Div (Num (n1-(m*n2)), Num (n2)), Sum (ss))
                                                                                        | Div (Num (m1), Num (m2)) -> (Div (Num ((n1*m2)-(m1*n2)), Num (m2*n2)), Sum (ss))
                                                                                    )   
                                                    | (Some (Sum (ss)), None) -> (Div (Num (n1), Num (n2)), Sum (ss))
                                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                                 )
        | (Prod (p), Var (x)) -> (
                                 match (transform_constraint_smt2_rec (Prod (p)) None None) with
                                    | (Some (Prod (ps)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (n) -> (Sum ([Prod (ps)] @ [Prod ([Num (-1); Var (x)])]), Num (0-n))
                                                                        | Div (Num (n1), Num (n2)) -> (Sum ([Prod (ps)] @ [Prod ([Num (-1); Var (x)])]), Div (Num (0-n1), Num (n2)))
                                                                      )   
                                    | (Some (Prod (ps)), None) -> (Sum ([Prod (ps)] @ [Prod ([Num (-1); Var (x)])]), Num (0))
                                    | (None, Some (ns)) -> (
                                                            match ns with 
                                                            | Num (n) -> (Prod ([Num (-1); Var (x)]), Num (0-n))
                                                            | Div (Num (n1), Num (n2)) -> (Prod ([Num (-1); Var (x)]), Div (Num (0-n1), Num (n2)))
                                                           )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Var (x), Prod (p)) -> (
                                 match (transform_constraint_smt2_rec (Prod (p)) None None) with
                                    | (Some (Prod (ps)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (n) -> (Num (0-n), Sum ([Prod (ps)] @ [Prod ([Num (-1); Var (x)])]))
                                                                        | Div (Num (n1), Num (n2)) -> (Div (Num (0-n1), Num (n2)), Sum ([Prod (ps)] @ [Prod ([Num (-1); Var (x)])]))
                                                                      )   
                                    | (Some (Prod (ps)), None) -> (Num (0), Sum ([Prod (ps)] @ [Prod ([Num (-1); Var (x)])]))
                                    | (None, Some (ns)) -> (
                                                            match ns with 
                                                            | Num (n) -> (Num (0-n), Prod ([Num (-1); Var (x)]))
                                                            | Div (Num (n1), Num (n2)) -> (Div (Num (0-n1), Num (n2)), Prod ([Num (-1); Var (x)]))
                                                           )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Prod (p), Num (n)) -> (
                                 match (transform_constraint_smt2_rec (Prod (p)) None None) with
                                    | (Some (Prod (ps)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (m) -> (Prod (ps), Num (n-m))
                                                                        | Div (Num (m1), Num (m2)) -> (Prod (ps), Div (Num ((n*m2)-m1), Num (m2)))
                                                                      )   
                                    | (Some (Prod (ps)), None) -> (Prod (ps), Num (n))
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                )
        | (Num (n), Prod (p)) -> (
                                 match (transform_constraint_smt2_rec (Prod (p)) None None) with
                                    | (Some (Prod (ps)), Some (ns)) -> (
                                                                       match ns with 
                                                                        | Num (m) -> (Num (n-m), Prod (ps))
                                                                        | Div (Num (m1), Num (m2)) -> (Div (Num ((n*m2)-m1), Num (m2)), Prod (ps))
                                                                      )   
                                    | (Some (Prod (ps)), None) -> (Num (n), Prod (ps))
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                 )
        | (Prod (p), Div (Num (n1), Num (n2))) -> (
                                                  match (transform_constraint_smt2_rec (Prod (p)) None None) with
                                                    | (Some (Prod (ps)), Some (ns)) -> (
                                                                                    match ns with 
                                                                                        | Num (m) -> (Prod (ps), Div (Num (n1-(m*n2)), Num (n2)))
                                                                                        | Div (Num (m1), Num (m2)) -> (Prod (ps), Div (Num ((n1*m2)-(m1*n2)), Num (m2*n2)))
                                                                                    )   
                                                    | (Some (Prod (ps)), None) -> (Prod (ps), Div (Num (n1), Num (n2)))
                                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                                 )
        | (Div (Num (n1), Num (n2)), Prod (p)) -> (
                                                  match (transform_constraint_smt2_rec (Prod (p)) None None) with
                                                    | (Some (Prod (ps)), Some (ns)) -> (
                                                                                    match ns with 
                                                                                        | Num (m) -> (Div (Num (n1-(m*n2)), Num (n2)), Prod (ps))
                                                                                        | Div (Num (m1), Num (m2)) -> (Div (Num ((n1*m2)-(m1*n2)), Num (m2*n2)), Prod (ps))
                                                                                    )   
                                                    | (Some (Prod (ps)), None) -> (Div (Num (n1), Num (n2)), Prod (ps))
                                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                                 )
        | (Sum (s), Prod (p)) -> (
                                  match (transform_constraint_smt2_rec (Sum (s)) None None, transform_constraint_smt2_rec (Prod (p)) None None) with
                                    | ((Some (Sum (ss)), Some (ns)), (Some (Prod (ps)), Some (ms))) -> (
                                                                                                        match (ns, ms) with 
                                                                                                            | (Num (n), Num (m)) -> (Sum (ss @ [negate_prod (Prod (ps))]), Num (m-n))
                                                                                                            | (Div (Num (n1), Num (n2)), Num (m)) -> (Sum (ss @ [negate_prod (Prod (ps))]), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                            | (Num (n), Div (Num (m1), Num (m2))) -> (Sum (ss @ [negate_prod (Prod (ps))]), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                            | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Sum (ss @ [negate_prod (Prod (ps))]), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                                        )   
                                    | ((Some (Sum (ss)), None), (Some (Prod (ps)), Some (ms))) -> (Sum (ss @ [Prod (ps @ [Num (-1)])]), ms)
                                    | ((Some (Sum (ss)), Some (ns)), (Some (Prod (ps)), None)) -> (
                                                                                                   match ns with 
                                                                                                    | Num (n) -> (Sum (ss @ [negate_prod (Prod (ps))]), Num (0-n))
                                                                                                    | Div (Num (n1), Num (n2)) -> (Sum (ss @ [negate_prod (Prod (ps))]), Div (Num (0-n1), Num (n2)))
                                                                                                  )
                                    | ((Some (Sum (ss)), None), (Some (Prod (ps)), None)) -> (Sum (ss @ [negate_prod (Prod (ps))]), Num (0))
                                    | ((Some (Sum (ss)), Some (ns)), (None, Some (ms))) -> (
                                                                                             match (ns, ms) with 
                                                                                                | (Num (n), Num (m)) -> (Sum (ss), Num (m-n))
                                                                                                | (Div (Num (n1), Num (n2)), Num (m)) -> (Sum (ss), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                | (Num (n), Div (Num (m1), Num (m2))) -> (Sum (ss), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Sum (ss), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                            ) 
                                    | ((None, Some (ns)), (Some (Prod (ps)), Some (ms))) -> (
                                                                                             match (ns, ms) with 
                                                                                                | (Num (n), Num (m)) -> (negate_prod (Prod (ps)), Num (m-n))
                                                                                                | (Div (Num (n1), Num (n2)), Num (m)) -> (negate_prod (Prod (ps)), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                | (Num (n), Div (Num (m1), Num (m2))) -> (negate_prod (Prod (ps)), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (negate_prod (Prod (ps)), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                            ) 
                                    | ((Some (Sum (ss)), None), (None, Some (ms))) -> (Sum (ss), ms)
                                    | ((None, Some (ns)), (Some (Prod (ps)), None)) -> (
                                                                                        match ns with 
                                                                                        | Num (n) -> (negate_prod (Prod (ps)), Num (0-n))
                                                                                        | Div (Num (n1), Num (n2)) -> (negate_prod (Prod (ps)), Div (Num (0-n1), Num (n2)))
                                                                                       )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                 )
        | (Prod (p), Sum (s)) -> (
                                  match (transform_constraint_smt2_rec (Sum (s)) None None, transform_constraint_smt2_rec (Prod (p)) None None) with
                                    | ((Some (Sum (ss)), Some (ns)), (Some (Prod (ps)), Some (ms))) -> ( 
                                                                                                        match (ns, ms) with 
                                                                                                            | (Num (n), Num (m)) -> (Num (m-n), Sum (ss @ [negate_prod (Prod (ps))]))
                                                                                                            | (Div (Num (n1), Num (n2)), Num (m)) -> (Div (Num ((m*n2)-n1), Num (n2)), Sum (ss @ [negate_prod (Prod (ps))]))
                                                                                                            | (Num (n), Div (Num (m1), Num (m2))) -> (Div (Num (m1-(n*m2)), Num (m2)), Sum (ss @ [negate_prod (Prod (ps))]))
                                                                                                            | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)), Sum (ss @ [negate_prod (Prod (ps))]))
                                                                                                        )   
                                    | ((Some (Sum (ss)), None), (Some (Prod (ps)), Some (ms))) -> (ms, Sum (ss @ [negate_prod (Prod (ps))]))
                                    | ((Some (Sum (ss)), Some (ns)), (Some (Prod (ps)), None)) -> ( 
                                                                                                   match ns with 
                                                                                                    | Num (n) -> (Num (0-n), Sum (ss @ [negate_prod (Prod (ps))]))
                                                                                                    | Div (Num (n1), Num (n2)) -> (Div (Num (0-n1), Num (n2)), Sum (ss @ [negate_prod (Prod (ps))]))
                                                                                                  )
                                    | ((Some (Sum (ss)), None), (Some (Prod (ps)), None)) -> (Num (0), Sum (ss @ [negate_prod (Prod (ps))]))
                                    | ((Some (Sum (ss)), Some (ns)), (None, Some (ms))) -> (
                                                                                             match (ns, ms) with 
                                                                                                | (Num (n), Num (m)) -> (Num (m-n), Sum (ss))
                                                                                                | (Div (Num (n1), Num (n2)), Num (m)) -> (Div (Num ((m*n2)-n1), Num (n2)), Sum (ss))
                                                                                                | (Num (n), Div (Num (m1), Num (m2))) -> (Div (Num (m1-(n*m2)), Num (m2)), Sum (ss))
                                                                                                | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)), Sum (ss))
                                                                                            ) 
                                    | ((None, Some (ns)), (Some (Prod (ps)), Some (ms))) -> (
                                                                                             match (ns, ms) with 
                                                                                                | (Num (n), Num (m)) -> (Num (m-n), negate_prod (Prod (ps)))
                                                                                                | (Div (Num (n1), Num (n2)), Num (m)) -> (Div (Num ((m*n2)-n1), Num (n2)), negate_prod (Prod (ps)))
                                                                                                | (Num (n), Div (Num (m1), Num (m2))) -> (Div (Num (m1-(n*m2)), Num (m2)), negate_prod (Prod (ps)))
                                                                                                | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)), negate_prod (Prod (ps)))
                                                                                            ) 
                                    | ((Some (Sum (ss)), None), (None, Some (ms))) -> (ms, Sum (ss))
                                    | ((None, Some (ns)), (Some (Prod (ps)), None)) -> (
                                                                                        match ns with 
                                                                                        | Num (n) -> (Num (0-n), negate_prod (Prod (ps)))
                                                                                        | Div (Num (n1), Num (n2)) -> (Div (Num (0-n1), Num (n2)), negate_prod (Prod (ps)))
                                                                                       )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                 )
        | (Sum (s1), Sum (s2)) -> (
                                   match (transform_constraint_smt2_rec (Sum (s1)) None None, transform_constraint_smt2_rec (Sum (s2)) None None) with
                                    | ((Some (Sum (ss1)), Some (ns)), (Some (Sum (ss2)), Some (ms))) -> (
                                                                                                        match (ns, ms) with 
                                                                                                            | (Num (n), Num (m)) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Num (m-n))
                                                                                                            | (Div (Num (n1), Num (n2)), Num (m)) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                            | (Num (n), Div (Num (m1), Num (m2))) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                            | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                                        )   
                                    | ((Some (Sum (ss1)), None), (Some (Sum (ss2)), Some (ms))) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), ms)
                                    | ((Some (Sum (ss1)), Some (ns)), (Some (Sum (ss2)), None)) -> (
                                                                                                   match ns with 
                                                                                                    | Num (n) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Num (0-n))
                                                                                                    | Div (Num (n1), Num (n2)) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Div (Num (0-n1), Num (n2)))
                                                                                                  )
                                    | ((Some (Sum (ss1)), None), (Some (Sum (ss2)), None)) -> (Sum (ss1 @ [Prod ([Sum (ss2)] @ [Num (-1)])]), Num (0))
                                    | ((Some (Sum (ss1)), Some (ns)), (None, Some (ms))) -> (
                                                                                             match (ns, ms) with 
                                                                                                | (Num (n), Num (m)) -> (Sum (ss1), Num (m-n))
                                                                                                | (Div (Num (n1), Num (n2)), Num (m)) -> (Sum (ss1), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                | (Num (n), Div (Num (m1), Num (m2))) -> (Sum (ss1), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Sum (ss1), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                            ) 
                                    | ((None, Some (ns)), (Some (Sum (ss2)), Some (ms))) -> (
                                                                                             match (ns, ms) with 
                                                                                                | (Num (n), Num (m)) -> (Prod ([Sum (ss2)] @ [Num (-1)]), Num (m-n))
                                                                                                | (Div (Num (n1), Num (n2)), Num (m)) -> (Prod ([Sum (ss2)] @ [Num (-1)]), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                | (Num (n), Div (Num (m1), Num (m2))) -> (Prod ([Sum (ss2)] @ [Num (-1)]), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Prod ([Sum (ss2)] @ [Num (-1)]), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                            ) 
                                    | ((Some (Sum (ss1)), None), (None, Some (ms))) -> (Sum (ss1), ms)
                                    | ((None, Some (ns)), (Some (Sum (ss2)), None)) -> (
                                                                                        match ns with 
                                                                                        | Num (n) -> (Prod ([Sum (ss2)] @ [Num (-1)]), Num (0-n))
                                                                                        | Div (Num (n1), Num (n2)) -> (Prod ([Sum (ss2)] @ [Num (-1)]), Div (Num (0-n1), Num (n2)))
                                                                                       )
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                  )
        | (Prod (p1), Prod (p2)) -> (
                                     match (transform_constraint_smt2_rec (Prod (p1)) None None, transform_constraint_smt2_rec (Prod (p2)) None None) with
                                    | ((Some (Prod (ps1)), Some (ns)), (Some (Prod (ps2)), Some (ms))) -> (
                                                                                                        match (ns, ms) with 
                                                                                                            | (Num (n), Num (m)) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Num (m-n))
                                                                                                            | (Div (Num (n1), Num (n2)), Num (m)) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Div (Num ((m*n2)-n1), Num (n2)))
                                                                                                            | (Num (n), Div (Num (m1), Num (m2))) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Div (Num (m1-(n*m2)), Num (m2)))
                                                                                                            | (Div (Num (n1), Num (n2)), Div (Num (m1), Num (m2))) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Div (Num ((m1*n2)-(n1*m2)), Num (n2*m2)))
                                                                                                        )   
                                    | ((Some (Prod (ps1)), None), (Some (Prod (ps2)), Some (ms))) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), ms)
                                    | ((Some (Prod (ps1)), Some (ns)), (Some (Prod (ps2)), None)) -> (
                                                                                                   match ns with 
                                                                                                    | Num (n) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Num (0-n))
                                                                                                    | Div (Num (n1), Num (n2)) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Div (Num (0-n1), Num (n2)))
                                                                                                  )
                                    | ((Some (Prod (ps1)), None), (Some (Prod (ps2)), None)) -> (Sum ([Prod (ps1)] @ [negate_prod (Prod (ps2))]), Num (0))
                                    | _ -> failwith "[Invalid argument] transform_constraint_smt2"
                                    )
        | _ -> failwith "[Invalid argument] transform_constraint_smt2";;

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
        | Prod ([p1; p2]) -> (
                              match prod_to_simplex_format_inc operator with 
                               | (Sum (s), _) -> op_to_simplex_format (Sum (s)) varlist varcount
                               | (Var (x), Num (n)) -> (
                                                        match (is_in_varlist varlist x) with 
                                                                | -1 -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                | m -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), varlist, varcount)   
                                                       )
                               | (Var (x), Div (Num (n1), Num (n2))) -> (
                                                                         match (is_in_varlist varlist x) with 
                                                                                | -1 -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                                | m -> ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)) (Simplex.nat_of_integer (big_int_of_int m))), varlist, varcount)   
                                                                        )
                             )
        | _ -> failwith "[Invalid argument] op_to_simplex_format";;


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
                                                                         match (transform_constraint_smt2 (Sum (s), Var (x))) with 
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
                                                                         match (transform_constraint_smt2 (Var (x), Sum (s))) with 
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
                                                                         match (transform_constraint_smt2 (Sum (s), Num (n))) with 
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
                                                                         match (transform_constraint_smt2 (Num (n), Sum (s))) with 
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
                                                                            match (transform_constraint_smt2 (Prod (p), Var (x))) with 
                                                                             | (prod, Num (n)) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Var (x), Prod (p))) with 
                                                                             | (Num (n), prod) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p), Num (n))) with 
                                                                             | (prod, Num (m)) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (m1), Num (m2))) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m1) (big_int_of_int m2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m1)) (big_int_of_int m2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )  
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Num (n), Prod (p))) with 
                                                                             | (Num (m), prod) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1)))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (m1), Num (m2)), prod) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m1) (big_int_of_int m2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m1)) (big_int_of_int m2)))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Prod (p))) with 
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
                                                                         match (transform_constraint_smt2 (Prod (p), Sum (s))) with 
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
                                                        | (Div (d1, d2), Var (x)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                               match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))),
                                                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.LT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Var (x), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) 
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])          
                                                                                                                | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])          
                                                                                                                | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])  
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Div (d1, d2), Num (n)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match (compare ((float_of_int n1) /. (float_of_int n2)) (float_of_int n)) with
                                                                                                                    | 1 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])    
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
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])  
                                                                                                                           )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s), Div (d1, d2)) -> (
                                                                                      match (transform_constraint_smt2 (Sum (s), Div (d1, d2))) with
                                                                                        | (sums, Num (n)) -> (
                                                                                                        match (op_to_simplex_format sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                                )
                                                                                  )
                                                        | (Div (d1, d2), Sum (s)) -> (
                                                                                      match (transform_constraint_smt2 (Div (d1, d2), Sum (s))) with
                                                                                        | (Num (n), sums) -> (
                                                                                                        match (op_to_simplex_format sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                            )
                                                                                  )
                                                        | (Prod (p), Div (d1, d2)) -> (
                                                                                       match (transform_constraint_smt2 (Prod (p), Div (d1, d2))) with
                                                                                        | (prod, Num (n)) -> (
                                                                                                        match (op_to_simplex_format prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                                )
                                                                                   )
                                                        | (Div (d1, d2), Prod (p)) -> (
                                                                                       match (transform_constraint_smt2 (Div (d1, d2), Prod (p))) with
                                                                                        | (Num (n), prod) -> (
                                                                                                        match (op_to_simplex_format prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                            match (op_to_simplex_format prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                            )
                                                                                   )
                                                        | (Div (d11, d12), Div (d21, d22)) -> (
                                                                                   match ((d11, d12), (d21, d22)) with 
                                                                                    | ((Num (n1d1), Num (n2d1)), (Num (n1d2), Num (n2d2))) -> (
                                                                                                    match (compare ((float_of_int n1d1) /. (float_of_int n2d1)) ((float_of_int n1d2) /. (float_of_int n2d2))) with
                                                                                                        | 1 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                            )
                                                                                                        | _ -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])    
                                                                                                            )
                                                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
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
                    | Constraint (Less (l, r)) -> ( 
                                                     match (l, r) with 
                                                        | (Var (x), Num (n)) -> 
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) 
                                                                                                                                                                               (cs @ [(c, v, d, dl)])       
                                                                            | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)])          
                                                                            | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.LT((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                            | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                           )
                                                        | (Num (n), Var (x)) ->
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                      (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)]) 
                                                                            | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))),
                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                            | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                       (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                            | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                         (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                           )
                                                        | (Var (x), Var (y)) ->
                                                                             (
                                                                             match (is_in_varlist varlist x) with 
                                                                              | -1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex.LTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                        | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex.GEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                        | (m, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                        | (m, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                      )   
                                                                              | m1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                                                     (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                        | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                                                     (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                        | (m2, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.LTPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                       (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                        | (m2, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GEQPP ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m1))), 
                                                                                                                                                                                       (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                      ) 
                                                                            )
                                                        | (Sum (s), Var (x)) -> 
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Var (x))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Var (x), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Var (x), Sum (s))) with
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                )
                                                                                                                  )
                                                                        )
                                                        | (Sum (s), Num (n)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Num (n))) with
                                                                            | (sums, Num (m)) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                            | (sums, Div (Num (m1), Num (m2))) -> (
                                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m1) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m1)) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                )
                                                                                                                    )
                                                                        )
                                                        | (Num (n), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Num (n), Sum (s))) with
                                                                            | (Num (m), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (m1), Num (m2)), sums) -> (
                                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int m1) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (m1)) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                )
                                                                                                                )
                                                                        )
                                                        | (Prod (p), Var (x)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Prod (p), Var (x))) with 
                                                                             | (prod, Num (n)) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Var (x), Prod (p))) with 
                                                                             | (Num (n), prod) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p), Num (n))) with 
                                                                             | (prod, Num (m)) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (m1), Num (m2))) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m1) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m1)) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )       
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Num (n), Prod (p))) with 
                                                                             | (Num (m), prod) -> (
                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (m1), Num (m2)), prod) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int m1) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (m1)) (big_int_of_int m2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Prod (p))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Prod (p), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Prod (p), Sum (s))) with
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                )
                                                                                                                  )
                                                                        )   
                                                        | (Div (d1, d2), Var (x)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                               match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)]) 
                                                                                                                | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))),
                                                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.LEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Var (x), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.LT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) 
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])    
                                                                                                                | (-1, false) -> to_simplex_format (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])  
                                                                                                                | (m, true) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [( Simplex.LT ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])       
                                                                                                                | (m, false) -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GEQ ((Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))), 
                                                                                                                                                                                                            (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])  
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Div (d1, d2), Num (n)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match (compare ((float_of_int n1) /. (float_of_int n2)) (float_of_int n)) with
                                                                                                                    | 1 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                           )
                                                                                                                    | 0 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])   
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Num (n), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match (compare (float_of_int n) ((float_of_int n1) /. (float_of_int n2))) with
                                                                                                                    | 1 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                           )
                                                                                                                    | 0 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)]) 
                                                                                                                           )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s), Div (d1, d2)) -> (
                                                                                      match (transform_constraint_smt2 (Sum (s), Div (d1, d2))) with
                                                                                        | (sums, Num (n)) -> (
                                                                                                        match (op_to_simplex_format sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                                )
                                                                                  )
                                                        | (Div (d1, d2), Sum (s)) -> (
                                                                                      match (transform_constraint_smt2 (Div (d1, d2), Sum (s))) with
                                                                                        | (Num (n), sums) -> (
                                                                                                        match (op_to_simplex_format sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)]) 
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                            match (op_to_simplex_format sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)]) 
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                            )
                                                                                  )
                                                        | (Prod (p), Div (d1, d2)) -> (
                                                                                       match (transform_constraint_smt2 (Prod (p), Div (d1, d2))) with
                                                                                        | (prod, Num (n)) -> (
                                                                                                        match (op_to_simplex_format prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                                )
                                                                                   )
                                                        | (Div (d1, d2), Prod (p)) -> (
                                                                                       match (transform_constraint_smt2 (Div (d1, d2), Prod (p))) with
                                                                                        | (Num (n), prod) -> (
                                                                                                        match (op_to_simplex_format prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                            | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                            match (op_to_simplex_format prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                                | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                            )
                                                                                                                            )
                                                                                   )
                                                        | (Div (d11, d12), Div (d21, d22)) -> (
                                                                                   match ((d11, d12), (d21, d22)) with 
                                                                                    | ((Num (n1d1), Num (n2d1)), (Num (n1d2), Num (n2d2))) -> (
                                                                                                    match (compare ((float_of_int n1d1) /. (float_of_int n2d1)) ((float_of_int n1d2) /. (float_of_int n2d2))) with
                                                                                                        | 1 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                            )
                                                                                                        | 0 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                            )
                                                                                                        | _ -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                                                | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                                        Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)]) 
                                                                                                            )
                                                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s1), Sum (s2)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s1), Sum (s2))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Prod (p1), Prod (p2)) -> 
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p1), Prod (p2))) with
                                                                            | (prod, Num (n)) -> (
                                                                                                match (op_to_simplex_format prod varlist varcount) with
                                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                    | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n)) (big_int_of_int 1))))]) (cs @ [(c, v, d, dl)])
                                                                                                                )
                                                                                                )
                                                                            | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.LT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n1) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                        | false -> to_simplex_format (Assignment (xs)) newlist newcount (result @ [(Simplex.GEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int (n1)) (big_int_of_int n2))))]) (cs @ [(c, v, d, dl)])
                                                                                                                                    )
                                                                                                                  )
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> (
                                                                                   match (compare n1 n2) with
                                                                                    | 1 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                           )
                                                                                    | 0 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                    Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                            | false -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                           )
                                                                                    | _ -> (
                                                                                            match v with 
                                                                                             | true -> to_simplex_format (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)])
                                                                                             | false -> to_simplex_format (Assignment (xs)) varlist varcount (result @ [(Simplex.GTPP (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0)), 
                                                                                                                                                                                      Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int 0))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                           )
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
                        | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                        | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount) 
                     )
        | Num (n) -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))), varlist, varcount)
        | Div (d1, d2) -> (
                           match (d1, d2) with 
                                | (Num (n1), Num (n2)) -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int 0))), varlist, varcount)
                                | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: divison of non-num_type"
                          )
        | Sum (s) -> ( 
                      match s with
                       | [x] -> op_to_simplex_format_inc x varlist varcount
                       | x :: xs -> (
                                     match (op_to_simplex_format_inc x varlist varcount) with
                                        | (s_lp, newlist_s, newcount_s) -> (
                                                                        match (op_to_simplex_format_inc (Sum (xs)) newlist_s newcount_s) with
                                                                            | (ss_lp, newlist, newcount) -> ((Simplex_Inc.plus_linear_poly s_lp ss_lp), newlist, newcount)
                                                                       )
                                    )
                       | [] -> failwith "[Invalid argument] op_to_simplex_format_inc: empty list Sum ([])"
                     )
        | Prod ([Var (x); Num (n)]) -> (
                                        match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount) 
                                       )               
        | Prod ([Num (n); Var (x)]) -> (
                                        match (is_in_varlist varlist x) with 
                                        | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                        | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount) 
                                       )       
        | Prod ([Var (x); Div (d1, d2)]) -> (
                                            match (d1, d2) with
                                                | (Num (n1), Num (n2)) -> (
                                                                            match (is_in_varlist varlist x) with 
                                                                            | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                            | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount) 
                                                                        ) 
                                                | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: division of non-num_type"
                                            )
        | Prod ([Div (d1, d2); Var (x)]) -> (
                                            match (d1, d2) with
                                                | (Num (n1), Num (n2)) -> (
                                                                            match (is_in_varlist varlist x) with 
                                                                            | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                            | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount) 
                                                                        ) 
                                                | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: division of non-num_type"
                                            )
        | Prod ([Var (_); Var (_)]) -> failwith "[Invalid argument] op_to_simplex_format_inc: constraint not linear"
        | Prod ([p1; p2]) -> ( 
                              match prod_to_simplex_format_inc operator with 
                               | (Sum (s), _) -> op_to_simplex_format_inc (Sum (s)) varlist varcount
                               | (Var (x), Num (n)) -> (
                                                        match (is_in_varlist varlist x) with 
                                                                | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount)   
                                                       )
                               | (Var (x), Div (Num (n1), Num (n2))) -> (
                                                                         match (is_in_varlist varlist x) with 
                                                                                | -1 -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), (varlist @ [(x, varcount + 1)]), (varcount + 1))
                                                                                | m -> ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2)) (Simplex_Inc.nat_of_integer (Z.of_int m))), varlist, varcount)   
                                                                        )
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
                                                                            | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) 
                                                                                                                                                                               (cs @ [(c, v, d, dl)])
                                                                                                                                                                               i_map                        
                                                                            | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)])    
                                                                                                                                                                               i_map              
                                                                            | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])       
                                                                                                                                                i_map
                                                                            | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])  
                                                                                                                                                 i_map
                                                                           )
                                                        | (Num (n), Var (x)) ->
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                      (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                               i_map
                                                                            | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))),
                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                                                i_map
                                                                            | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                       (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                i_map
                                                                            | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                         (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                 i_map
                                                                           )
                                                        | (Var (x), Var (y)) ->
                                                                             (
                                                                             match (is_in_varlist varlist x) with 
                                                                              | -1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                 i_map
                                                                                        | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                 i_map
                                                                                        | (m, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                          i_map
                                                                                        | (m, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                          i_map
                                                                                      )   
                                                                              | m1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                                                     (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                           i_map
                                                                                        | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                                                     (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                           i_map
                                                                                        | (m2, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                       (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                                                                                             i_map
                                                                                        | (m2, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                       (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                                                                                             i_map
                                                                                      )
                                                                            )
                                                        | (Sum (s), Var (x)) -> 
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Var (x))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Var (x), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Var (x), Sum (s))) with
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                  )
                                                                        )
                                                        | (Sum (s), Num (n)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Num (n))) with
                                                                            | (sums, Num (m)) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (sums, Div (Num (m1), Num (m2))) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                    )
                                                                        )
                                                        | (Num (n), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Num (n), Sum (s))) with
                                                                            | (Num (m), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (m1), Num (m2)), sums) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                )
                                                                        )
                                                        | (Prod (p), Var (x)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Prod (p), Var (x))) with 
                                                                             | (prod, Num (n)) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Var (x), Prod (p))) with 
                                                                             | (Num (n), prod) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p), Num (n))) with 
                                                                             | (prod, Num (m)) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (m1), Num (m2))) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Num (n), Prod (p))) with 
                                                                             | (Num (m), prod) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (m1), Num (m2)), prod) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Prod (p))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Prod (p), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Prod (p), Sum (s))) with
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                  )
                                                                        )   
                                                        | (Div (d1, d2), Var (x)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                               match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                i_map
                                                                                                                | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))),
                                                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                                                    i_map
                                                                                                                | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                    i_map
                                                                                                                | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                    i_map
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Var (x), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) 
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                i_map                        
                                                                                                                | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])    
                                                                                                                                                                                                                i_map              
                                                                                                                | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])       
                                                                                                                                                                                    i_map
                                                                                                                | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
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
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
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
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                            i_map
                                                                                                                           )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s), Div (d1, d2)) -> (
                                                                                      match (transform_constraint_smt2 (Sum (s), Div (d1, d2))) with
                                                                                        | (sums, Num (n)) -> (
                                                                                                        match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                                )
                                                                                  )
                                                        | (Div (d1, d2), Sum (s)) -> (
                                                                                      match (transform_constraint_smt2 (Div (d1, d2), Sum (s))) with
                                                                                        | (Num (n), sums) -> (
                                                                                                        match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                            )
                                                                                  )
                                                        | (Prod (p), Div (d1, d2)) -> (
                                                                                       match (transform_constraint_smt2 (Prod (p), Div (d1, d2))) with
                                                                                        | (prod, Num (n)) -> (
                                                                                                        match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                                )
                                                                                   )
                                                        | (Div (d1, d2), Prod (p)) -> (
                                                                                       match (transform_constraint_smt2 (Div (d1, d2), Prod (p))) with
                                                                                        | (Num (n), prod) -> (
                                                                                                        match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                            match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                            )
                                                                                   )
                                                        | (Div (d11, d12), Div (d21, d22)) -> (
                                                                                   match ((d11, d12), (d21, d22)) with 
                                                                                    | ((Num (n1d1), Num (n2d1)), (Num (n1d2), Num (n2d2))) -> (
                                                                                                    match (compare ((float_of_int n1d1) /. (float_of_int n2d1)) ((float_of_int n1d2) /. (float_of_int n2d2))) with
                                                                                                        | 1 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                        Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                                                                            i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                            )
                                                                                                        | _ -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                        Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                i_map
                                                                                                            )
                                                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s1), Sum (s2)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s1), Sum (s2))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Prod (p1), Prod (p2)) -> 
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p1), Prod (p2))) with
                                                                            | (prod, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> (
                                                                                   match (compare n1 n2) with
                                                                                    | 1 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                                                                                           i_map
                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                           )
                                                                                    | _ -> (
                                                                                            match v with 
                                                                                             | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                             | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                      Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])      
                                                                                                                                                             i_map
                                                                                           )
                                                                                  )
                                                    )
                    | Constraint (Less (l, r)) -> ( 
                                                     match (l, r) with 
                                                        | (Var (x), Num (n)) -> 
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) 
                                                                                                                                                                               (cs @ [(c, v, d, dl)])
                                                                                                                                                                               i_map                        
                                                                            | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                       (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)])    
                                                                                                                                                                               i_map              
                                                                            | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])       
                                                                                                                                                i_map
                                                                            | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])  
                                                                                                                                                 i_map
                                                                           )
                                                        | (Num (n), Var (x)) ->
                                                                           (
                                                                            match ((is_in_varlist varlist x), v) with
                                                                            | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                      (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                                               (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                               i_map
                                                                            | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))),
                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                                                i_map
                                                                            | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                       (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                i_map
                                                                            | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                         (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))])
                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                 i_map
                                                                           )
                                                        | (Var (x), Var (y)) ->
                                                                             (
                                                                             match (is_in_varlist varlist x) with 
                                                                              | -1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                 i_map
                                                                                        | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)] @ [(y, varcount + 2)]) (varcount + 2) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                           (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 2))))))])
                                                                                                                                                                                                                 (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                 i_map
                                                                                        | (m, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                          i_map
                                                                                        | (m, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                    (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m)))))])
                                                                                                                                                                                          (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                          i_map
                                                                                      )   
                                                                              | m1 -> (
                                                                                       match ((is_in_varlist varlist y), v) with 
                                                                                        | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                                                     (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                           i_map
                                                                                        | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(y, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                                                     (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1))))))])
                                                                                                                                                                                           (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                           i_map
                                                                                        | (m2, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LTPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                       (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                                                                                             i_map
                                                                                        | (m2, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQPP ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m1))), 
                                                                                                                                                                                       (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m2)))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])
                                                                                                                                                             i_map
                                                                                      ) 
                                                                            )
                                                        | (Sum (s), Var (x)) -> 
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Var (x))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Var (x), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Var (x), Sum (s))) with
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                  )
                                                                        )
                                                        | (Sum (s), Num (n)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Num (n))) with
                                                                            | (sums, Num (m)) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (sums, Div (Num (m1), Num (m2))) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                    )
                                                                        )
                                                        | (Num (n), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Num (n), Sum (s))) with
                                                                            | (Num (m), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (m1), Num (m2)), sums) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                )
                                                                        )
                                                        | (Prod (p), Var (x)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Prod (p), Var (x))) with 
                                                                             | (prod, Num (n)) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Var (x), Prod (p)) ->
                                                                           ( 
                                                                            match (transform_constraint_smt2 (Var (x), Prod (p))) with 
                                                                             | (Num (n), prod) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Prod (p), Num (n)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p), Num (n))) with 
                                                                             | (prod, Num (m)) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (prod, Div (Num (m1), Num (m2))) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (transform_constraint_smt2 (Num (n), Prod (p))) with 
                                                                             | (Num (m), prod) -> (
                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                    (
                                                                                                                        match v with 
                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    )
                                                                                                  )
                                                                             | (Div (Num (m1), Num (m2)), prod) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int m1) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (m1)) (Z.of_int m2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                   )
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s), Prod (p))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Prod (p), Sum (s)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Prod (p), Sum (s))) with
                                                                            | (Num (n), sums) -> (
                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                               (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                               )
                                                                                                )
                                                                            | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                                (
                                                                                                                                    match v with 
                                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                )
                                                                                                                  )
                                                                        )   
                                                        | (Div (d1, d2), Var (x)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                               match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)]) 
                                                                                                                                                                                i_map
                                                                                                                | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))),
                                                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                                                    i_map
                                                                                                                | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                    i_map
                                                                                                                | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                    (cs @ [(c, v, d, dl)])
                                                                                                                                                    i_map
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Var (x), Div (d1, d2)) -> (
                                                                                   match (d1, d2) with 
                                                                                    | (Num (n1), Num (n2)) -> (
                                                                                                                match ((is_in_varlist varlist x), v) with
                                                                                                                | (-1, true) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) 
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])
                                                                                                                                                                                                                i_map                        
                                                                                                                | (-1, false) -> to_simplex_format_inc (Assignment (xs)) (varlist @ [(x, varcount + 1)]) (varcount + 1) (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int (varcount + 1)))), 
                                                                                                                                                                                                                                        (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
                                                                                                                                                                                                                (cs @ [(c, v, d, dl)])    
                                                                                                                                                                                                                i_map              
                                                                                                                | (m, true) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))])
                                                                                                                                                                                    (cs @ [(c, v, d, dl)])       
                                                                                                                                                                                    i_map
                                                                                                                | (m, false) -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ ((Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int m))), 
                                                                                                                                                                                                            (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))])
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
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | 0 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
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
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | 0 -> (
                                                                                                                            match v with   
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                                        (cs @ [(c, v, d, dl)])
                                                                                                                                                                                        i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                           )
                                                                                                                    | _ -> (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
                                                                                                                                                                                            (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                            i_map
                                                                                                                           )
                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s), Div (d1, d2)) -> (
                                                                                      match (transform_constraint_smt2 (Sum (s), Div (d1, d2))) with
                                                                                        | (sums, Num (n)) -> (
                                                                                                        match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                                )
                                                                                  )
                                                        | (Div (d1, d2), Sum (s)) -> (
                                                                                      match (transform_constraint_smt2 (Div (d1, d2), Sum (s))) with
                                                                                        | (Num (n), sums) -> (
                                                                                                        match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                        | (s_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), sums) -> (
                                                                                                                            match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                            | (s_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                            )
                                                                                  )
                                                        | (Prod (p), Div (d1, d2)) -> (
                                                                                       match (transform_constraint_smt2 (Prod (p), Div (d1, d2))) with
                                                                                        | (prod, Num (n)) -> (
                                                                                                        match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                            match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                                )
                                                                                   )
                                                        | (Div (d1, d2), Prod (p)) -> (
                                                                                       match (transform_constraint_smt2 (Div (d1, d2), Prod (p))) with
                                                                                        | (Num (n), prod) -> (
                                                                                                        match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                        | (p_lp, newlist, newcount) -> 
                                                                                                                        (
                                                                                                                            match v with 
                                                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                        )
                                                                                                            )
                                                                                        | (Div (Num (n1), Num (n2)), prod) -> (
                                                                                                                            match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                            | (p_lp, newlist, newcount) -> 
                                                                                                                                            (
                                                                                                                                                match v with 
                                                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.LEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                            )
                                                                                                                            )
                                                                                   )
                                                        | (Div (d11, d12), Div (d21, d22)) -> (
                                                                                   match ((d11, d12), (d21, d22)) with 
                                                                                    | ((Num (n1d1), Num (n2d1)), (Num (n1d2), Num (n2d2))) -> (
                                                                                                    match (compare ((float_of_int n1d1) /. (float_of_int n2d1)) ((float_of_int n1d2) /. (float_of_int n2d2))) with
                                                                                                        | 1 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                        Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                                                                            i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                            )
                                                                                                        | 0 -> (
                                                                                                                match v with   
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                        Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                                            (cs @ [(c, v, d, dl)])
                                                                                                                                                                            i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                            )
                                                                                                        | _ -> (
                                                                                                                match v with 
                                                                                                                | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                                                | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                                        Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
                                                                                                                                                                                (cs @ [(c, v, d, dl)])      
                                                                                                                                                                                i_map
                                                                                                            )
                                                                                                                                              )
                                                                                    | _ -> failwith "[Invalid argument] op_to_simplex_format_inc: Division contains non-num_type"
                                                                                  )
                                                        | (Sum (s1), Sum (s2)) ->
                                                                        ( 
                                                                         match (transform_constraint_smt2 (Sum (s1), Sum (s2))) with
                                                                            | (sums, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (sums, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc sums varlist varcount) with
                                                                                                                    | (s_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (s_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                        )
                                                        | (Prod (p1), Prod (p2)) -> 
                                                                           (
                                                                            match (transform_constraint_smt2 (Prod (p1), Prod (p2))) with
                                                                            | (prod, Num (n)) -> (
                                                                                                match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                | (p_lp, newlist, newcount) -> 
                                                                                                                (
                                                                                                                    match v with 
                                                                                                                    | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                    | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n)) (Z.of_int 1))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                )
                                                                                                )
                                                                            | (prod, Div (Num (n1), Num (n2))) -> (
                                                                                                                    match (op_to_simplex_format_inc prod varlist varcount) with
                                                                                                                    | (p_lp, newlist, newcount) -> 
                                                                                                                                    (
                                                                                                                                        match v with 
                                                                                                                                        | true -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.LT (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int n1) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                        | false -> to_simplex_format_inc (Assignment (xs)) newlist newcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GEQ (p_lp, (Simplex_Inc.rat_of_int_pair (Z.of_int (n1)) (Z.of_int n2))))]) (cs @ [(c, v, d, dl)]) i_map
                                                                                                                                    )
                                                                                                                  )
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> (
                                                                                   match (compare n1 n2) with
                                                                                    | 1 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                                                                                           i_map
                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                           )
                                                                                    | 0 -> (
                                                                                            match v with   
                                                                                            | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Atom c) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                    Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))]) 
                                                                                                                                                           (cs @ [(c, v, d, dl)])
                                                                                                                                                           i_map
                                                                                            | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                           )
                                                                                    | _ -> (
                                                                                            match v with 
                                                                                             | true -> to_simplex_format_inc (Assignment (xs)) varlist varcount result (cs @ [(c, v, d, dl)]) i_map
                                                                                             | false -> to_simplex_format_inc (Assignment (xs)) varlist varcount (result @ [(Simplex_Inc.nat_of_integer (Z.of_int (Tseitin.Index_Map_Opt.find (Not (Atom c)) i_map)), Simplex_Inc.GTPP (Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0)), 
                                                                                                                                                                                      Simplex_Inc.lp_monom (Simplex_Inc.rat_of_int_pair (Z.of_int 1) (Z.of_int 1)) (Simplex_Inc.nat_of_integer (Z.of_int 0))))])
                                                                                                                                                             (cs @ [(c, v, d, dl)])      
                                                                                                                                                             i_map
                                                                                           )
                                                                                  )
                                                    )

                   );;

let to_simplex_format_inc_init assignment i_map = to_simplex_format_inc assignment [] 0 [] [] i_map;;

