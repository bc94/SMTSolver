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
                                                                            match (op_to_simplex_format (Sum (s)) varlist varcount) with
                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> [Simplex.LEQPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (-1, false) -> [Simplex.GTPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (m, true) -> [Simplex.LEQPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                        | (m, false) -> [Simplex.GTPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                    )
                                                                           )
                                                        | (Var (x), Sum (s)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Sum (s)) varlist varcount) with
                                                                                | (s_lp, newlist, newcount) -> 
                                                                                                    (
                                                                                                     match ((is_in_varlist newlist x), v) with 
                                                                                                        | (-1, true) -> [Simplex.GTPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (-1, false) -> [Simplex.LEQPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int (newcount + 1)))))] @ (to_simplex_format (Assignment (xs)) (newlist @ [(x, newcount + 1)]) (newcount + 1))
                                                                                                        | (m, true) -> [Simplex.GTPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                        | (m, false) -> [Simplex.LEQPP (s_lp, (Simplex.lp_monom (Simplex.rat_of_int_pair (big_int_of_int 1) (big_int_of_int 1)) (Simplex.nat_of_integer (big_int_of_int m))))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                                    )
                                                                           )
                                                        | (Sum (s), Num (n)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Sum (s)) varlist varcount) with
                                                                                | (s_lp, newlist, newcount) -> [Simplex.LEQ (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)                               
                                                                           )
                                                        | (Num (n), Sum (s)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Sum (s)) varlist varcount) with
                                                                                | (s_lp, newlist, newcount) -> [Simplex.GT (s_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)                         
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
                                                                                | (p_lp, newlist, newcount) -> [Simplex.LEQ (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)                       
                                                                           )
                                                        | (Num (n), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist, newcount) -> [Simplex.GT (p_lp, (Simplex.rat_of_int_pair (big_int_of_int n) (big_int_of_int 1)))] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                           )
                                                        | (Sum (s), Prod (p)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Sum (s)) varlist varcount) with
                                                                                | (s_lp, newlist_s, newcount_s) -> 
                                                                                    (
                                                                                     match (op_to_simplex_format (Prod (p)) newlist_s newcount_s) with
                                                                                        | (p_lp, newlist, newcount) -> [Simplex.LEQPP (s_lp, p_lp)] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                    )
                                                                           )     
                                                        | (Prod (p), Sum (s)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p)) varlist varcount) with
                                                                                | (p_lp, newlist_p, newcount_p) -> 
                                                                                    (
                                                                                     match (op_to_simplex_format (Sum (s)) newlist_p newcount_p) with
                                                                                        | (s_lp, newlist, newcount) -> [Simplex.GTPP (s_lp, p_lp)] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                    )
                                                                           )     
                                                        | (Sum (s1), Sum (s2)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Sum (s1)) varlist varcount) with
                                                                                | (s1_lp, newlist_s1, newcount_s1) -> 
                                                                                    (
                                                                                     match (op_to_simplex_format (Sum (s2)) newlist_s1 newcount_s1) with
                                                                                        | (s2_lp, newlist, newcount) -> [Simplex.GTPP (s1_lp, s2_lp)] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                    )
                                                                           )     
                                                        | (Prod (p1), Prod (p2)) ->
                                                                           (
                                                                            match (op_to_simplex_format (Prod (p1)) varlist varcount) with
                                                                                | (p1_lp, newlist_p1, newcount_p1) -> 
                                                                                    (
                                                                                     match (op_to_simplex_format (Prod (p2)) newlist_p1 newcount_p1) with
                                                                                        | (p2_lp, newlist, newcount) -> [Simplex.GTPP (p1_lp, p2_lp)] @ (to_simplex_format (Assignment (xs)) newlist newcount)
                                                                                    )
                                                                           )     
                                                        | (Num (n1), Num (n2)) -> to_simplex_format (Assignment (xs)) varlist varcount
                                                    )
                   );;

let to_simplex_format_init assignment = to_simplex_format assignment [] 0;;