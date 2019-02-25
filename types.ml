(************************************)
(* Types for the actual constraints *)
(************************************)

type num_type = Sum of num_type list
              | Prod of num_type list
              | Div of num_type * num_type
              | Num of int
              | Var of string;;

type less_equal = LessEq of num_type * num_type
                | Less of num_type * num_type
                | Eq of num_type * num_type;;

type constraint_n = Constraint of less_equal
                  | Index of int
                  | AuxVar of int
                  | RVar of string;;

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

(*************************)
(* Variable substitution *)
(*************************)

(* This type is a necessary wrapper around list elements *)
(* of the list that is constructed during parsing of *)
(* 'let' statements in the 'smt2' file format and is *)
(* then used to do variable substitution according to *)
(* the parsed 'let' statements *)

type substitution = SubstNum of (num_type * num_type)
                  | SubstElem of (num_type * element)
                  | SubstForm of formula;;

type subst_list = SubstList of substitution list;;




