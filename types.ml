(* Types for the propositional SAT Solver *)

type literal = Var of int
             | Not of literal;;

type clause = Clause of int * literal list;;

type formula = Formula of clause list;;

type assignment = Assignment of literal list;;

(* Types for the SMT constraints *)

type number = Num of int
            | Var of int;;

type sum = Sum of number * number 
         | Sum of sum * number
         | Sum of number * sum
         | Sum of sum * sum
         | Sum of number * product 
         | Sum of product * number
         | Sum of product * product

and product = Prod of number * number 
         | Prod of sum * number
         | Prod of number * sum
         | Prod of sum * sum
         | Prod of number * product 
         | Prod of product * number
         | Prod of product * product;; 

type func = Fun of sum 
          | Fun of product;;

type less_equal = LessEq of func * number
                | LessEq of number * number;;

type less = Less of number * number;;

type constraint_n = Constraint of int * less_equal
                   | Constraint of int * less;;
                   | Not of constraint_n;;






