(************************************)
(* Types for the actual constraints *)
(************************************)

type num_type = Sum of num_type list
              | Prod of num_type list
              | Num of int
              | Var of string;;

type less_equal = LessEq of num_type * num_type
                | Eq of num_type * num_type;;

type constraint_n = Constraint of less_equal
                  | Index of int
                  | AuxVar of int;;

(**************************)
(* Boolean operators etc. *)
(**************************)

(* The first bool is the assigned truth value *)
(* the second bool is 'true' if the variable's *)
(* assignment was the result of the 'decide' rule *)
(* and 'false'  otherwise and the final value is *)
(* the current decision level *)
type assignment = Assignment of (constraint_n * bool * bool * int) list;;

type element = Atom of constraint_n
             | Conjunction of element list
             | Disjunction of element list
             | Not of element;;

type formula = Formula of element;;





