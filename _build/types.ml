(* Types for the actual constraints *)

type num_type = Sum of num_type list
              | Prod of num_type list
              | Num of int
              | Var of string;;

type less_equal = LessEq of num_type * num_type;;

type constraint_n = Constraint of less_equal;;

(* Boolean operators etc. *)

type clause = Clause of constraint_n list;;

type assignment = Assignment of constraint_n * bool list;;

type element = Atom of constraint_n
             | Conjunction of element list
             | Disjunction of element list
             | Not of element;;

type formula = Formula of element;;





