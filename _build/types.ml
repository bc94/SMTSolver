(* Types for the actual constraints *)

type num_type = Sum of num_type list
              | Prod of num_type list
              | Num of int
              | Var of string;;

type less_equal = LessEq of num_type * num_type;;

(* The first element (int) represents the (propositional) 
   variable name of the constraint when processed by the 
   SAT Solver *)

type constraint_n = Constraint of int * less_equal;;

(* Boolean operators etc. *)

type clause = Clause of constraint_n list;;

type assignment = Assignment of constraint_n list;;

type element = Atom of constraint_n
             | Conjunction of element list
             | Disjunction of element list
             | Not of element;;

type formula = Formula of element;;





