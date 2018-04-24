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
        | _ -> failwith "[Invalid formula]: transform_elem";;

let tseitin_transformation_n f n_aux n_last = 
    match f with
        | Formula (x) -> (
                          match (transform_elem x n_aux n_last) with
                            | (xs, n) -> Formula (Conjunction ([Atom (AuxVar n_aux)] @ xs))
                            | _ -> failwith "[Invalid formula]: tseitin_transformation_n"
                         )
        | _ -> failwith "[Invalid formula]: tseitin_transformation_n";;

let tseitin_transformation f = tseitin_transformation_n f 0 0;;