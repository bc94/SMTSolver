module Index_Map = Map.Make(String);;
module Inv_Map = Map.Make(struct type t = int let compare = compare end);;

open Types
open List

(* Tseitin transformation to transform a formula into CNF.*)

(* Argument f is the formula and arguments n_aux and n_last are *) 
(* counting variables used to introduce the new variables needed *)
(* in the transformation algorithm *)

let remove_last xs = rev (tl (rev xs));;

let rec transform_elem (e : element) (n_aux : int) (n_last : int) : (element list * int) =
    match e with
        | Not (x) -> (
                      match (transform_elem x (n_last + 1) (n_last + 1)) with 
                        | (xs, n) -> ([Disjunction ([(Atom (AuxVar n_aux)); (Atom (AuxVar (n_last + 1)))])] @ 
                                      [Disjunction ([Not (Atom (AuxVar n_aux)); Not (Atom (AuxVar (n_last + 1)))])] @
                                      xs,
                                      n)
                        | _ -> failwith "[Invalid formula]: transform_elem"
                     )                  
        | Conjunction ([]) -> ([], n_last)
        | Conjunction (xs) -> (
                               match (length xs) with
                                | 2 -> (
                                        match (transform_elem (hd (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                        match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                        )
                                        )
                                | 1 -> (transform_elem (hd xs) n_aux n_last)
                                | _ -> (
                                        match (transform_elem (Conjunction (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                        match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                        )
                                       )
                              )
        | Disjunction ([]) -> ([], n_last)      
        | Disjunction (xs) -> (
                               match (length xs) with 
                                | 2 -> (
                                        match (transform_elem (hd (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                           match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                          )
                                       )
                                | 1 -> (transform_elem (hd xs) n_aux n_last)
                                | _ -> (
                                        match (transform_elem (Disjunction (remove_last xs)) (n_last + 1) (n_last + 2)) with
                                            | (ys, n1) -> (
                                                        match (transform_elem (hd (rev xs)) (n_last + 2) (n1)) with 
                                                            | (zs, n2) -> ([Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                                                                           [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                           [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                                                                           ys @
                                                                           zs,
                                                                           n2)
                                                        )
                                       )
                              )
        | Atom (x) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom x])] @ 
                       [Disjunction ([Not (Atom x); Atom (AuxVar n_aux)])],
                       n_last)
        | _ -> failwith "[Invalid argument]: transform_elem";;

let tseitin_transformation_n f n_aux n_last = 
    match f with
        | Formula (x) -> (
                          match (transform_elem x n_aux n_last) with
                            | (xs, n) -> Formula (Conjunction ([Atom (AuxVar n_aux)] @ xs))
                            | _ -> failwith "[Invalid argument]: tseitin_transformation_n"
                         )
        | _ -> failwith "[Invalid formula]: tseitin_transformation_n";;

let tseitin_transformation f = tseitin_transformation_n f 0 0;;


(* A version of the tseitin transformation that additionally extracts all constraints *)
(* in order to construct the tableau for the incremental simplex procedure *)

let rec transform_elem_inc e cs i_map inv_map i n_aux n_last =
    match e with
        | Not (x) -> (
                      match (transform_elem_inc x cs i_map inv_map i (n_last + 1) (n_last + 1)) with 
                        | (xs, n, cs_new, i_map_new, inv_map_new, i_new) -> ([Disjunction ([(Atom (AuxVar n_aux)); (Atom (AuxVar (n_last + 1)))])] @ 
                                                                [Disjunction ([Not (Atom (AuxVar n_aux)); Not (Atom (AuxVar (n_last + 1)))])] @
                                                                xs,
                                                                n,
                                                                cs_new,
                                                                i_map_new,
                                                                inv_map_new,
                                                                i_new)
                        | _ -> failwith "[Invalid formula]: transform_elem"
                     )                  
        | Conjunction ([]) -> ([], n_last, cs, i_map, inv_map, i)
        | Conjunction (xs) -> (
                               match (length xs) with
                                | 2 -> (
                                        match (transform_elem_inc (hd (remove_last xs)) cs i_map inv_map i (n_last + 1) (n_last + 2)) with
                                            | (ys, n1, cs_n, i_map_n, inv_map_n, i_n) -> (
                                                              match (transform_elem_inc (hd (rev xs)) cs_n i_map_n inv_map_n i_n (n_last + 2) (n1)) with 
                                                                | (zs, n2, cs_new, i_map_new, inv_map_new, i_new) -> 
                                                                        ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                                                                         [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                                                                         [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                         ys @
                                                                         zs,
                                                                         n2,
                                                                         cs_new,
                                                                         i_map_new,
                                                                         inv_map_new,
                                                                         i_new)
                                                             )
                                        )
                                | 1 -> (transform_elem_inc (hd xs) cs i_map inv_map i n_aux n_last)
                                | _ -> (
                                        match (transform_elem_inc (Conjunction (remove_last xs)) cs i_map inv_map i (n_last + 1) (n_last + 2)) with
                                            | (ys, n1, cs_n, i_map_n, inv_map_n, i_n) -> 
                                                        (
                                                         match (transform_elem_inc (hd (rev xs)) cs_n i_map_n inv_map_n i_n (n_last + 2) (n1)) with 
                                                            | (zs, n2, cs_new, i_map_new, inv_map_new, i_new) -> 
                                                                ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1))])] @ 
                                                                 [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 2))])] @ 
                                                                 [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1))); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                 ys @
                                                                 zs,
                                                                 n2,
                                                                 cs_new,
                                                                 i_map_new,
                                                                 inv_map_new,
                                                                 i_new)
                                                        )
                                       )
                              )
        | Disjunction ([]) -> ([], n_last, cs, i_map, inv_map, i)      
        | Disjunction (xs) -> (
                               match (length xs) with 
                                | 2 -> (
                                        match (transform_elem_inc (hd (remove_last xs)) cs i_map inv_map i (n_last + 1) (n_last + 2)) with
                                            | (ys, n1, cs_n, i_map_n, inv_map_n, i_n) -> (
                                                           match (transform_elem_inc (hd (rev xs)) cs_n i_map_n inv_map_n i_n (n_last + 2) (n1)) with 
                                                            | (zs, n2, cs_new, i_map_new, inv_map_new, i_new) -> 
                                                                ([Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                                                                 [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                 [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                                                                 ys @
                                                                 zs,
                                                                 n2,
                                                                 cs_new,
                                                                 i_map_new,
                                                                 inv_map_new,
                                                                 i_new)
                                                          )
                                       )
                                | 1 -> (transform_elem_inc (hd xs) cs i_map inv_map i n_aux n_last)
                                | _ -> (
                                        match (transform_elem_inc (Disjunction (remove_last xs)) cs i_map inv_map i (n_last + 1) (n_last + 2)) with
                                            | (ys, n1, cs_n, i_map_n, inv_map_n, i_n) -> (
                                                        match (transform_elem_inc (hd (rev xs)) cs_n i_map_n inv_map_n i_n (n_last + 2) (n1)) with 
                                                            | (zs, n2, cs_new, i_map_new, inv_map_new, i_new) -> 
                                                                ([Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 1)))])] @ 
                                                                 [Disjunction ([Atom (AuxVar n_aux); Not (Atom (AuxVar (n_last + 2)))])] @ 
                                                                 [Disjunction ([Not (Atom (AuxVar n_aux)); Atom (AuxVar (n_last + 1)); Atom (AuxVar (n_last + 2))])] @ 
                                                                 ys @
                                                                 zs,
                                                                 n2,
                                                                 cs_new,
                                                                 i_map_new,
                                                                 inv_map_new,
                                                                 i_new)
                                                        )
                                       )
                              )
        | Atom (x) -> ([Disjunction ([Not (Atom (AuxVar n_aux)); Atom x])] @ 
                       [Disjunction ([Not (Atom x); Atom (AuxVar n_aux)])],
                       n_last,
                       (cs @ [(x, true, false, 0)] @ [(x, false, false, 0)]),
                       (Index_Map.add ("-" ^ Printing.print_constraint_n x) (i + 1) (Index_Map.add (Printing.print_constraint_n x) i (i_map))),
                       (Inv_Map.add (i + 1) (x, false, false, 0) (Inv_Map.add i (x, true, false, 0) inv_map)),
                       i + 2)
        | _ -> failwith "[Invalid argument]: transform_elem_inc";;

let tseitin_transformation_inc_n f n_aux n_last = 
    match f with
        | Formula (x) -> (
                          match (transform_elem_inc x [] Index_Map.empty Inv_Map.empty 0 n_aux n_last) with
                            | (xs, n, cs, i_map, inv_map, i) -> (Formula (Conjunction ([Atom (AuxVar n_aux)] @ xs)), Assignment (cs), i_map, inv_map)
                            | _ -> failwith "[Invalid argument]: tseitin_transformation_inc_n"
                         )
        | _ -> failwith "[Invalid argument]: tseitin_transformation_inc_n";;

let tseitin_transformation_inc f = tseitin_transformation_inc_n f 0 0;;