(* This formalization has been copied from the weblink 
   http://argo.matf.bg.ac.rs/ which is provided in:

   Mirko Spasic and Filip Maric.
   Formalization of Incremental Simplex Algorithm by Stepwise Refinement.
   Formal Methods 2012, LNCS 7436, pages 434--449, 2012.

   The theories have been adjusted to work with the current Isabelle version by R. Thiemann.
*)
theory Simplex_Export
  imports 
  Algebra 
  LinearPolyMaps 
  RelChain 
  QDelta
  "HOL-Library.RBT_Mapping"
  HOL.Order_Relation
  "HOL-Library.Permutation"
  "HOL-Library.Code_Target_Numeral" 
begin

text{* Linear constraints are of the form @{text "p \<bowtie> c"} or @{text
"p\<^sub>1 \<bowtie> p\<^sub>2"}, where @{text "p"}, @{text "p\<^sub>1"}, and @{text "p\<^sub>2"}, are
linear polynomials, @{text "c"} is a rational constant and @{text "\<bowtie> \<in>
{<, >, \<le>, \<ge>, =}"}. Their abstract syntax is given by the @{text
"constraint"} type, and semantics is given by the relation @{text
"\<Turnstile>\<^sub>c"}, defined straightforwardly by primitive recursion over the
@{text "constraint"} type. The list of contraints is satisfied,
denoted by @{text "\<Turnstile>\<^sub>c\<^sub>s"}, if all constraints are. *}

datatype constraint = LT linear_poly rat    
                    | GT linear_poly rat 
                    | LEQ linear_poly rat   
                    | GEQ linear_poly rat
                    | EQ linear_poly rat
                    | LTPP linear_poly linear_poly
                    | GTPP linear_poly linear_poly
                    | LEQPP linear_poly linear_poly
                    | GEQPP linear_poly linear_poly
                    | EQPP linear_poly linear_poly

primrec
  satisfies_constraint :: "rat valuation \<Rightarrow> constraint \<Rightarrow> bool"  (infixl "\<Turnstile>\<^sub>c" 100) where
  "v \<Turnstile>\<^sub>c LT l r \<longleftrightarrow> l\<lbrace>v\<rbrace> < r"    
| "v \<Turnstile>\<^sub>c GT l r \<longleftrightarrow> l\<lbrace>v\<rbrace> > r" 
| "v \<Turnstile>\<^sub>c LEQ l r \<longleftrightarrow> l\<lbrace>v\<rbrace> \<le> r"
| "v \<Turnstile>\<^sub>c GEQ l r \<longleftrightarrow> l\<lbrace>v\<rbrace> \<ge>  r"
| "v \<Turnstile>\<^sub>c EQ l r \<longleftrightarrow> l\<lbrace>v\<rbrace> = r"
| "v \<Turnstile>\<^sub>c LTPP l1 l2 \<longleftrightarrow> l1\<lbrace>v\<rbrace> < l2\<lbrace>v\<rbrace>"
| "v \<Turnstile>\<^sub>c GTPP l1 l2 \<longleftrightarrow> l1\<lbrace>v\<rbrace> > l2\<lbrace>v\<rbrace>"
| "v \<Turnstile>\<^sub>c LEQPP l1 l2 \<longleftrightarrow> l1\<lbrace>v\<rbrace> \<le> l2\<lbrace>v\<rbrace>"
| "v \<Turnstile>\<^sub>c GEQPP l1 l2 \<longleftrightarrow> l1\<lbrace>v\<rbrace> \<ge> l2\<lbrace>v\<rbrace>"
| "v \<Turnstile>\<^sub>c EQPP l1 l2 \<longleftrightarrow> l1\<lbrace>v\<rbrace> = l2\<lbrace>v\<rbrace>"


abbreviation satisfies_constraints :: "rat valuation \<Rightarrow> constraint list \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>c\<^sub>s" 100) where
"v \<Turnstile>\<^sub>c\<^sub>s cs \<equiv> \<forall> c \<in> set cs. v \<Turnstile>\<^sub>c c"

subsection{*Procedure Specification*}

text{* The specification for the satisfiability check procedure is given by: *}
locale Solve = 
  -- {* --- Decide if the given list of constraints is satisfiable. Return the satisfiability status
     and, in the satisfiable case, one satisfying valuation. *}
  fixes solve :: "constraint list \<Rightarrow> bool \<times> rat valuation option"
  -- {* --- If the status @{text True} is returned, then returned valuation
      satisfies all constraints. *}
  assumes (*<*) simplex_sat: (*>*) "let (sat, v) = solve cs in sat \<longrightarrow> the v \<Turnstile>\<^sub>c\<^sub>s cs" 
  -- {* --- If the status @{text False} is returned, then constraints are
     unsatisfiable. *}
  assumes (*<*) simplex_unsat: (*>*) "let (sat, v) = solve cs in \<not> sat \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s cs)"
(*<*)
(*<*)abbreviation look where "look \<equiv> Mapping.lookup"(*>*)
(*<*)abbreviation upd where "upd \<equiv> Mapping.update"(*>*)
(* RT: changed "undefined" to "0" in map2fun, led to runtime crashes before *)
definition map2fun:: "(var, 'a :: zero) mapping \<Rightarrow> var \<Rightarrow> 'a" where
 "map2fun v \<equiv> \<lambda>x. case look v x of None \<Rightarrow> 0 | Some y \<Rightarrow> y"
syntax
  "_map2fun" :: "(var, 'a) mapping \<Rightarrow> var \<Rightarrow> 'a"  ("\<langle>_\<rangle>")
translations
  "\<langle>v\<rangle>" == "CONST map2fun v"

lemma map2fun_def':
  "\<langle>v\<rangle> x \<equiv> case Mapping.lookup v x of None \<Rightarrow> 0 | Some y \<Rightarrow> y"
  by (auto simp add: map2fun_def)
(*>*)

text{* Note that the above specification requires returning a
valuation (defined as a HOL function), which is not efficiently
executable. In order to enable more efficient data structures for
representing valuations, a refinement of this specification is needed
and the function @{text "solve"} is replaced by the function @{text
"solve_exec"} returning optional @{text "(var, rat) mapping"} instead
of @{text "var \<Rightarrow> rat"} function. This way, efficient data structures
for representing mappings can be easily plugged-in during code
generation \cite{florian-refinement}. A conversion from the @{text
"mapping"} datatype to HOL function is denoted by @{text "\<langle>_\<rangle>"} and
given by: @{thm map2fun_def'[no_vars]}. *}

(*<*)
locale SolveExec = 
  fixes solve_exec :: "constraint list \<Rightarrow> bool \<times> (var, rat) mapping option"
  assumes (*<*) simplex_sat0: (*>*) "let (sat, v) = solve_exec cs in sat \<longrightarrow> \<langle>the v\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs"
  assumes (*<*) simplex_unsat0: (*>*) "let (sat, v) = solve_exec cs in \<not> sat \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s cs)"
begin
definition solve where
  "solve cs \<equiv> let (sat, v) = solve_exec cs 
                 in if sat then (True, Some \<langle>the v\<rangle>) 
                    else (False, None)"
end

sublocale SolveExec < Solve solve
proof
  fix cs
  show "let (sat, v) = solve cs in sat \<longrightarrow> the v \<Turnstile>\<^sub>c\<^sub>s cs"
    unfolding solve_def Let_def split_def
    using simplex_sat0[of cs]
    by auto
next
  fix cs
  show "let (sat, v) = solve cs in \<not> sat \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>c\<^sub>s cs)"
    unfolding solve_def Let_def split_def
    using simplex_unsat0[of cs]
    by auto
qed
(*>*)

subsection{* Handling Strict Inequalities *}

text{* The first step of the procedure is removing all equalities and
strict inequalities. Equalities can be easily rewritten to non-strict
inequalities. Removing strict inequalities can be done by replacing
the list of constraints by a new one, formulated over an extension
@{text "\<rat>'"} of the space of rationals @{text "\<rat>"}. @{text "\<rat>'"} must
have a structure of a linearly ordered vector space over @{text "\<rat>"}
(represented by the type class @{text "lrv"}) and must guarantee that
if some non-strict constraints are satisfied in @{text "\<rat>'"}, then
there is a satisfying valuation for the original constraints in @{text
"\<rat>"}. Our final implementation uses the @{text "\<rat>\<^sub>\<delta>"} space, defined in
\cite{simplex-rad} (basic idea is to replace @{text "p < c"} by @{text
"p \<le> c - \<delta>"} and @{text "p > c"} by @{text "p \<ge> c + \<delta>"} for a symbolic
parameter @{text \<delta>}). So, all constraints are reduced to the form
@{text "p \<bowtie> b"}, where @{text "p"} is a linear polynomial (still over
@{text "\<rat>"}), @{text "b"} is constant from @{text "\<rat>'"} and @{text "\<bowtie>
\<in> {\<le>, \<ge>}"}. The non-strict constraints are represented by the type
@{text "'a ns_constraint"}, and their semantics is denoted by @{text
"\<Turnstile>\<^sub>n\<^sub>s"} and @{text "\<Turnstile>\<^sub>n\<^sub>s\<^sub>s"}. *}
datatype 'a ns_constraint = LEQ_ns linear_poly 'a    |    GEQ_ns linear_poly 'a 

(*<*) primrec satisfiable_ns_constraint :: "'a::lrv valuation \<Rightarrow> 'a ns_constraint \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>n\<^sub>s" 100) where (*>*) 
"v \<Turnstile>\<^sub>n\<^sub>s LEQ_ns l r \<longleftrightarrow> l\<lbrace>v\<rbrace> \<le> r"    |    "v \<Turnstile>\<^sub>n\<^sub>s GEQ_ns l r \<longleftrightarrow> l\<lbrace>v\<rbrace> \<ge> r"

(*<*) abbreviation satisfies_ns_constraints :: "'a::lrv valuation \<Rightarrow> 'a ns_constraint list \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>n\<^sub>s\<^sub>s " 100) where (*>*)
"v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s cs \<equiv> \<forall> c \<in> set cs. v \<Turnstile>\<^sub>n\<^sub>s c"

text{* Specification of reduction of constraints to non-strict form is given by: *}
locale To_ns = 
  -- {* --- Convert a constraint list to an equisatisfiable non-strict constraint list. *}
  fixes to_ns :: "constraint list \<Rightarrow> 'a::lrv ns_constraint list"
  assumes (*<*) to_ns_unsat: (*>*) "v  \<Turnstile>\<^sub>c\<^sub>s cs \<Longrightarrow> \<exists> v'. v' \<Turnstile>\<^sub>n\<^sub>s\<^sub>s to_ns cs"
  -- {* --- Convert the valuation that satisfies all non-strict constraints to the valuation that
   satisfies all initial constraints. *}
  fixes from_ns :: "(var, 'a) mapping \<Rightarrow> 'a ns_constraint list \<Rightarrow> (var, rat) mapping"
  assumes (*<*) to_ns_sat: (*>*) "\<langle>v'\<rangle>  \<Turnstile>\<^sub>n\<^sub>s\<^sub>s to_ns cs \<Longrightarrow> \<langle>from_ns v' (to_ns cs)\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs"
(*<*)
locale Solve_exec_ns = 
  fixes solve_exec_ns :: "'a::lrv ns_constraint list \<Rightarrow> bool \<times> (var, 'a) mapping option"
  assumes (*<*)simplex_ns_sat: (*>*) "let (sat, v) = solve_exec_ns cs in sat \<longrightarrow> \<langle>the v\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s cs"
  assumes (*<*)simplex_ns_unsat: (*>*) "let (sat, v) = solve_exec_ns cs in \<not> sat \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s cs)"
(*>*)

text{* After the transformation, the procedure is reduced to solving
only the non-strict constraints, implemented in the @{text
"solve_exec_ns"} function having an analogous specification to the
@{text "solve"} function. If @{text "to_ns"}, @{text "from_ns"} and
@{text "solve_exec_ns"} are available, the @{text "solve_exec"}
function can be easily defined and it can be easily shown that this
definition satisfies its specification (also analogous to @{text solve}). 
*}
(*<*)
locale SolveExec' = To_ns to_ns from_ns + Solve_exec_ns solve_exec_ns for
  to_ns:: "constraint list \<Rightarrow> 'a::lrv ns_constraint list" and
  from_ns :: "(var, 'a) mapping \<Rightarrow> 'a ns_constraint list \<Rightarrow> (var, rat) mapping" and
  solve_exec_ns :: "'a ns_constraint list \<Rightarrow> bool \<times> (var, 'a) mapping option"
begin
(*>*)
(*<*)definition solve_exec where (*>*)
  "solve_exec cs \<equiv> let cs' = to_ns cs; (sat, v) = solve_exec_ns cs' in
               if sat then (True, Some (from_ns (the v) cs')) else (False, None)"
(*<*)
end
(*>*)
(*<*)
sublocale SolveExec' < SolveExec solve_exec
proof
  fix cs
  show "let (sat, v) = solve_exec cs in sat \<longrightarrow> \<langle>the v\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs"
    using simplex_ns_sat[of "to_ns cs"] to_ns_sat[of cs]
    by (auto simp add: solve_exec_def Let_def split: if_splits)
next
  fix cs
  show "let (sat, v) = solve_exec cs in \<not> sat \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>c\<^sub>s cs)"
    using simplex_ns_unsat[of "to_ns cs"] to_ns_unsat[of cs]
    by (force simp add: solve_exec_def Let_def split: if_splits)
qed
(*>*)

subsection{* Preprocessing *}

text{* The next step in the procedure rewrites a list of non-strict
constraints into an equisatisfiable form consisting of a list of
linear equations (called the \emph{tableau}) and of a list of
\emph{atoms} of the form @{text "x\<^sub>i \<bowtie> b\<^sub>i"} where @{text "x\<^sub>i"} is a
variable and @{text "b\<^sub>i"} is a constant (from the extension field). The
transformation is straightforward and introduces auxiliary variables
for linear polynomials occurring in the initial formula. For example,
@{text "[x\<^sub>1 + x\<^sub>2 \<le> b\<^sub>1, x\<^sub>1 + x\<^sub>2 \<ge> b\<^sub>2, x\<^sub>2 \<ge> b\<^sub>3]"} can be transformed to
the tableau @{text "[x\<^sub>3 = x\<^sub>1 + x\<^sub>2]"} and atoms @{text "[x\<^sub>3 \<le> b\<^sub>1, x\<^sub>3 \<ge>
b\<^sub>2, x\<^sub>2 \<ge> b\<^sub>3]"}. *}

(*<*)
type_synonym eq = "var \<times> linear_poly"
primrec lhs :: "eq \<Rightarrow> var" where "lhs (l, r) = l"
primrec rhs :: "eq \<Rightarrow> linear_poly" where "rhs (l, r) = r"
abbreviation rvars_eq :: "eq \<Rightarrow> var set" where
 "rvars_eq eq \<equiv> vars (rhs eq)"
(*>*)
(*<*)
definition satisfies_eq :: "'a::rational_vector valuation \<Rightarrow> eq \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>e" 100) where
 "v \<Turnstile>\<^sub>e eq \<equiv> v (lhs eq) = (rhs eq)\<lbrace>v\<rbrace>"
lemma satisfies_eq_iff: "v \<Turnstile>\<^sub>e (x, p) \<equiv> v x = p\<lbrace>v\<rbrace>" 
by (simp add: satisfies_eq_def)
(*>*)

(*<*)
type_synonym tableau ="eq list"
(*>*)
(*<*)
definition satisfies_tableau ::"'a::rational_vector valuation \<Rightarrow> tableau \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>t" 100) where
  "v \<Turnstile>\<^sub>t t \<equiv> \<forall> e \<in> set t. v \<Turnstile>\<^sub>e e"
(*>*)
(*<*)
definition lvars :: "tableau \<Rightarrow> var set" where 
  "lvars t = set (map lhs t)"
definition rvars :: "tableau \<Rightarrow> var set" where
  "rvars t = \<Union> set (map rvars_eq t)"
abbreviation tvars where "tvars t \<equiv> lvars t \<union> rvars t" 
(*>*)
(*<*)
definition normalized_tableau :: "tableau \<Rightarrow> bool" ("\<triangle>") where
"normalized_tableau t \<equiv> distinct (map lhs t) \<and> lvars t \<inter> rvars t = {}"
(*>*)
text{* Equations are of the form @{text "x = p"}, where @{text "x"} is
a variable and @{text "p"} is a polynomial, and are represented by the
type @{text "eq = var \<times> linear_poly"}. Semantics of equations is given
by @{thm satisfies_eq_iff[no_vars]}. Tableau is represented as a list
of equations, by the type @{text "tableau = eq list"}. Semantics for a
tableau is given by @{thm satisfies_tableau_def[no_vars]}. Functions
@{text lvars} and @{text rvars} return sets of variables appearing on
the left hand side (lhs) and the right hand side (rhs) of a
tableau. Lhs variables are called \emph{basic} while rhs variables are
called \emph{non-basic} variables. A tableau @{text t} is
\emph{normalized} (denoted by @{term "\<triangle> t"}) iff no variable occurs on
the lhs of two equations in a tableau and if sets of lhs and rhs
variables are distinct.  *}
(*<*)
lemma normalized_tableau_unique_eq_for_lvar:
  assumes "\<triangle> t"
  shows "\<forall> x \<in> lvars t. \<exists>! p. (x, p) \<in> set t"
proof (safe)
  fix x
  assume "x \<in> lvars t"
  thus "\<exists>p. (x, p) \<in> set t"
    unfolding lvars_def
    by auto
next
  fix x p1 p2
  assume *: "(x, p1) \<in> set t" "(x, p2) \<in> set t"
  thus "p1 = p2"
    using `\<triangle> t`
    unfolding normalized_tableau_def
    by (force simp add: distinct_map inj_on_def)
qed

lemma recalc_tableau_lvars:
  assumes "\<triangle> t"
  shows "\<forall> v. \<exists> v'. (\<forall> x \<in> rvars t. v x = v' x) \<and> v' \<Turnstile>\<^sub>t t"
proof
  fix v
  let ?v' = "\<lambda> x. if x \<in> lvars t then (THE p. (x, p) \<in> set t) \<lbrace> v \<rbrace> else v x"
  show "\<exists> v'. (\<forall> x \<in> rvars t. v x = v' x) \<and> v' \<Turnstile>\<^sub>t t"
  proof (rule_tac x="?v'" in exI, rule conjI)
    show "\<forall>x\<in>rvars t. v x = ?v' x"
      using `\<triangle> t`
      unfolding normalized_tableau_def
      by auto
    show "?v' \<Turnstile>\<^sub>t t"
      unfolding satisfies_tableau_def satisfies_eq_def 
    proof
      fix e
      assume "e \<in> set t"
      obtain l r where e: "e = (l,r)" by force
      show "?v' (lhs e) = rhs e \<lbrace> ?v' \<rbrace>"
      proof-
        have "(lhs e, rhs e) \<in> set t"
          using `e \<in> set t` e by auto
        have "\<exists>!p. (lhs e, p) \<in> set t"
          using `\<triangle> t` normalized_tableau_unique_eq_for_lvar[of t]
          using `e \<in> set t`
          unfolding lvars_def
          by auto
        
        let ?p = "THE p. (lhs e, p) \<in> set t"
        have "(lhs e, ?p) \<in> set t"
          apply (rule theI')
          using `\<exists>!p. (lhs e, p) \<in> set t`
          by auto
        hence "?p = rhs e"
          using `(lhs e, rhs e) \<in> set t`
          using `\<exists>!p. (lhs e, p) \<in> set t`
          by auto
        moreover
        have "?v' (lhs e) = ?p \<lbrace> v \<rbrace>"
          using `e \<in> set t`
          unfolding lvars_def
          by simp
        moreover
        have "rhs e \<lbrace> ?v' \<rbrace> = rhs e \<lbrace> v \<rbrace>"
          apply (rule valuate_depend)
          using `\<triangle> t` `e \<in> set t`
          unfolding normalized_tableau_def
          by (auto simp add: lvars_def rvars_def)
        ultimately
        show ?thesis
          by auto
      qed
    qed
  qed
qed

lemma tableau_perm:
  assumes "lvars t1 = lvars t2" "rvars t1 = rvars t2"
  "\<triangle> t1" "\<triangle> t2" "\<And> v::'a::lrv valuation. v \<Turnstile>\<^sub>t t1 \<longleftrightarrow> v \<Turnstile>\<^sub>t t2"
  shows "t1 <~~> t2"
proof-
  {
    fix t1 t2
    assume "lvars t1 = lvars t2" "rvars t1 = rvars t2"
  "\<triangle> t1" "\<And> v::'a::lrv valuation. v \<Turnstile>\<^sub>t t1 \<longleftrightarrow> v \<Turnstile>\<^sub>t t2"
    have "set t1 \<subseteq> set t2"
    proof (safe)
      fix a b
      assume "(a, b) \<in> set t1"
      hence "a \<in> lvars t1"
        unfolding lvars_def
        by force
      hence "a \<in> lvars t2"
        using `lvars t1 = lvars t2`
        by simp
      then obtain b' where "(a, b') \<in> set t2"
        unfolding lvars_def
        by force
      have "\<forall>v::'a valuation. \<exists>v'. (\<forall>x\<in>vars (b - b'). v' x = v x) \<and> (b - b') \<lbrace> v' \<rbrace> = 0"
      proof
        fix v::"'a valuation"
        obtain v' where "v' \<Turnstile>\<^sub>t t1" "\<forall> x \<in> rvars t1. v x = v' x"
          using recalc_tableau_lvars[of t1] `\<triangle> t1`
          by auto
        have "v' \<Turnstile>\<^sub>t t2"
          using `v' \<Turnstile>\<^sub>t t1` `\<And> v. v \<Turnstile>\<^sub>t t1 \<longleftrightarrow> v \<Turnstile>\<^sub>t t2`
          by simp
        have "b \<lbrace>v'\<rbrace> = b' \<lbrace>v'\<rbrace>"
          using `(a, b) \<in> set t1` `v' \<Turnstile>\<^sub>t t1`
          using `(a, b') \<in> set t2` `v' \<Turnstile>\<^sub>t t2`
          unfolding satisfies_tableau_def satisfies_eq_def
          by force
        hence "(b - b') \<lbrace>v'\<rbrace> = 0"
          using valuate_minus[of b b' v']
          by auto
        moreover
        have "vars b \<subseteq> rvars t1" "vars b' \<subseteq> rvars t1"
          using `(a, b) \<in> set t1` `(a, b') \<in> set t2` `rvars t1 = rvars t2`
          unfolding rvars_def
          by force+
        hence "vars (b - b') \<subseteq> rvars t1"
          using vars_minus[of b b']
          by blast
        hence "\<forall>x\<in>vars (b - b'). v' x = v x"
          using `\<forall> x \<in> rvars t1. v x = v' x`
          by auto
        ultimately
        show "\<exists>v'. (\<forall>x\<in>vars (b - b'). v' x = v x) \<and> (b - b') \<lbrace> v' \<rbrace> = 0"
          by auto
      qed
      hence "b = b'"
        using all_val[of "b - b'"]
        by simp
      thus "(a, b) \<in> set t2"
        using `(a, b') \<in> set t2`
        by simp
    qed
  }
  note * = this
  have "set t1 = set t2"
    using *[of t1 t2] *[of t2 t1]
    using assms
    by auto
  moreover
  have "distinct t1" "distinct t2"
    using `\<triangle> t1` `\<triangle> t2`
    unfolding normalized_tableau_def
    by (auto simp add: distinct_map)
  ultimately
  show ?thesis
    by (auto simp add: set_eq_iff_mset_eq_distinct mset_eq_perm)
qed
(*>*)

text{* Elementary atoms are represented by the type @{text "'a atom"}
and semantics for atoms and sets of atoms is denoted by @{text "\<Turnstile>\<^sub>a"} and
@{text "\<Turnstile>\<^sub>a\<^sub>s"} and given by:  
*}

datatype 'a atom  = Leq var 'a    |    Geq var 'a
(*<*)
primrec atom_var::"'a atom \<Rightarrow> var" where
  "atom_var (Leq var a) = var" 
| "atom_var (Geq var a) = var"
(*>*)


(*<*) primrec satisfies_atom :: "'a::linorder valuation \<Rightarrow> 'a atom \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>a" 100) where  (*>*)
"v \<Turnstile>\<^sub>a Leq x c \<longleftrightarrow> v x \<le> c"    |    "v \<Turnstile>\<^sub>a Geq x c \<longleftrightarrow> v x \<ge> c"

(*<*) definition satisfies_atom_set :: "'a::linorder valuation \<Rightarrow> 'a atom set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>a\<^sub>s" 100) where (*>*)
"v \<Turnstile>\<^sub>a\<^sub>s as \<equiv> \<forall> a \<in> as. v \<Turnstile>\<^sub>a a"

text{* 
The specification of the preprocessing function is given by: *}
locale Preprocess = fixes preprocess::"'a::lrv ns_constraint list \<Rightarrow> tableau\<times>'a atom list"
  assumes
   -- {* --- The returned tableau is always normalized. *}
  (*<*)preprocess_tableau_normalized: (*>*)"let (t, as) = preprocess cs in \<triangle> t" (*<*)and(*>*)

   -- {* --- Tableau and atoms are equisatisfiable with starting non-strict constraints. *}
  (*<*)preprocess_sat: (*>*)"let (t, as) = preprocess cs in v \<Turnstile>\<^sub>a\<^sub>s set as \<and> v \<Turnstile>\<^sub>t t \<longrightarrow> v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s cs" (*<*)and(*>*)

  (*<*)preprocess_unsat: (*>*)"let (t, as) = preprocess cs in v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s cs \<longrightarrow> (\<exists> v'. v' \<Turnstile>\<^sub>a\<^sub>s set as \<and> v' \<Turnstile>\<^sub>t t)"
(*<*)
locale AssertAll = 
  fixes assert_all :: "tableau \<Rightarrow> 'a::lrv atom list \<Rightarrow> bool \<times> (var, 'a)mapping option"
  assumes (*<*)assert_all_sat: (*>*) "\<triangle> t \<Longrightarrow> let (sat, v) = assert_all t as in sat \<longrightarrow> \<langle>the v\<rangle> \<Turnstile>\<^sub>t t \<and> \<langle>the v\<rangle> \<Turnstile>\<^sub>a\<^sub>s set as"
  assumes (*<*)assert_all_unsat: (*>*) "\<triangle> t \<Longrightarrow> let (sat, v) = assert_all t as in \<not> sat \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s set as)"
(*>*)

text{* Once the preprocessing is done and tableau and atoms are
obtained, their satisfiability is checked by the
@{text assert_all} function. Its precondition is that the starting
tableau is normalized, and its specification is analogue to the one for the 
@{text "solve"} function. If @{text "preprocess"} and @{text "assert_all"}
are available, the  @{text "solve_exec_ns"} can be defined, and it
can easily be shown that this definition satisfies the specification. *}
(*<*)
locale Solve_exec_ns' = Preprocess preprocess + AssertAll assert_all for 
  preprocess:: "'a::lrv ns_constraint list \<Rightarrow> tableau \<times> ('a atom list)" and
  assert_all :: "tableau \<Rightarrow> 'a::lrv atom list \<Rightarrow> bool \<times> (var, 'a) mapping option"
begin
definition solve_exec_ns where
(*>*)
  "solve_exec_ns s \<equiv> let (t, as) = preprocess s in assert_all t as"
(*<*)
end
(*>*)
(*<*)
sublocale Solve_exec_ns' < Solve_exec_ns solve_exec_ns
proof
  fix qs
  show "let (sat, v) = solve_exec_ns qs in sat \<longrightarrow> \<langle>the v\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s qs"
    using assert_all_sat[of "fst (preprocess qs)" "snd (preprocess qs)"] preprocess_sat
    using preprocess_tableau_normalized 
    by (auto simp add: solve_exec_ns_def split_def Let_def)
next
  fix qs
  show "let (sat, v) = solve_exec_ns qs in \<not> sat \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s qs)"
    using assert_all_unsat[of "fst (preprocess qs)" "snd (preprocess qs)"] preprocess_unsat
    using  preprocess_tableau_normalized
    by (force simp add: solve_exec_ns_def split_def Let_def)
qed
(*>*)

subsection{* Incrementally Asserting Atoms *}

text{* The function @{term assert_all} can be implemented by
iteratively asserting one by one atom from the given list of atoms. 
*}

(*<*)type_synonym 'a bounds = "var \<rightharpoonup> 'a"(*>*)

text{* Asserted atoms will be stored in a form of \emph{bounds} for a
given variable. Bounds are of the form @{text "l\<^sub>i \<le> x\<^sub>i \<le> u\<^sub>i"}, where
@{text "l\<^sub>i"} and @{text "u\<^sub>i"} and are either scalars or $\pm
\infty$. Each time a new atom is asserted, a bound for the
corresponding variable is updated (checking for conflict with the
previous bounds). Since bounds for a variable can be either finite or
$\pm \infty$, they are represented by (partial) maps from variables to
values (@{text "'a bounds = var \<rightharpoonup> 'a"}). Upper and lower bounds are
represented separately. Infinite bounds map to @{term None} and this
is reflected in the semantics:

\begin{small}
@{text "c \<ge>\<^sub>u\<^sub>b b \<longleftrightarrow> case b of None \<Rightarrow> False | Some b' \<Rightarrow> c \<ge> b'"}

@{text "c \<le>\<^sub>u\<^sub>b b \<longleftrightarrow> case b of None \<Rightarrow> True | Some b' \<Rightarrow> c \<le> b'"}
\end{small}

\noindent Strict comparisons, and comparisons with lower bounds are performed similiarly.
*}
(*<*)
abbreviation (input) le where
"le lt x y \<equiv> lt x y \<or> x = y"
definition geub ("\<unrhd>\<^sub>u\<^sub>b") where
"\<unrhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> le lt b' c"
definition gtub ("\<rhd>\<^sub>u\<^sub>b") where
"\<rhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> lt b' c"
definition leub ("\<unlhd>\<^sub>u\<^sub>b") where
"\<unlhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> le lt c b'"
definition ltub ("\<lhd>\<^sub>u\<^sub>b") where
"\<lhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> lt c b'"
definition lelb ("\<unlhd>\<^sub>l\<^sub>b") where
"\<unlhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> le lt c b'"
definition ltlb ("\<lhd>\<^sub>l\<^sub>b") where
"\<lhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> lt c b'"
definition gelb ("\<unrhd>\<^sub>l\<^sub>b") where
"\<unrhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> le lt b' c"
definition gtlb ("\<rhd>\<^sub>l\<^sub>b") where
"\<rhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> lt b' c"
(*>*)
(*<*)
definition ge_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<ge>\<^sub>u\<^sub>b" 100) where 
"c \<ge>\<^sub>u\<^sub>b b = \<unrhd>\<^sub>u\<^sub>b (op <) c b"
definition gt_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl ">\<^sub>u\<^sub>b" 100) where 
"c >\<^sub>u\<^sub>b b = \<rhd>\<^sub>u\<^sub>b (op <) c b"
definition le_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<le>\<^sub>u\<^sub>b" 100) where 
"c \<le>\<^sub>u\<^sub>b b = \<unlhd>\<^sub>u\<^sub>b (op <) c b"
definition lt_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "<\<^sub>u\<^sub>b" 100) where 
"c <\<^sub>u\<^sub>b b = \<lhd>\<^sub>u\<^sub>b (op <) c b"
definition le_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<le>\<^sub>l\<^sub>b" 100) where
"c \<le>\<^sub>l\<^sub>b b = \<unlhd>\<^sub>l\<^sub>b (op <) c b"
definition lt_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "<\<^sub>l\<^sub>b" 100) where
"c <\<^sub>l\<^sub>b b = \<lhd>\<^sub>l\<^sub>b (op <) c b"
definition ge_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<ge>\<^sub>l\<^sub>b" 100) where
"c \<ge>\<^sub>l\<^sub>b b = \<unrhd>\<^sub>l\<^sub>b (op <) c b"
definition gt_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl ">\<^sub>l\<^sub>b" 100) where
"c >\<^sub>l\<^sub>b b = \<rhd>\<^sub>l\<^sub>b (op <) c b"
(*>*)
(*<*)
lemmas bound_compare'_defs = 
geub_def gtub_def leub_def ltub_def 
gelb_def gtlb_def lelb_def ltlb_def 

lemmas bound_compare''_defs = 
ge_ubound_def gt_ubound_def le_ubound_def lt_ubound_def 
le_lbound_def lt_lbound_def ge_lbound_def gt_lbound_def

lemmas bound_compare_defs = bound_compare'_defs bound_compare''_defs
(*>*)
(*<*)
lemma opposite_dir [simp]: 
  "\<unlhd>\<^sub>l\<^sub>b (op >) a b = \<unrhd>\<^sub>u\<^sub>b (op <) a b"
  "\<unlhd>\<^sub>u\<^sub>b (op >) a b = \<unrhd>\<^sub>l\<^sub>b (op <) a b"
  "\<unrhd>\<^sub>l\<^sub>b (op >) a b = \<unlhd>\<^sub>u\<^sub>b (op <) a b"
  "\<unrhd>\<^sub>u\<^sub>b (op >) a b = \<unlhd>\<^sub>l\<^sub>b (op <) a b"
  "\<lhd>\<^sub>l\<^sub>b (op >) a b = \<rhd>\<^sub>u\<^sub>b (op <) a b"
  "\<lhd>\<^sub>u\<^sub>b (op >) a b = \<rhd>\<^sub>l\<^sub>b (op <) a b"
  "\<rhd>\<^sub>l\<^sub>b (op >) a b = \<lhd>\<^sub>u\<^sub>b (op <) a b"
  "\<rhd>\<^sub>u\<^sub>b (op >) a b = \<lhd>\<^sub>l\<^sub>b (op <) a b"
  by (case_tac[!] b) (auto simp add: bound_compare'_defs)
(*>*)
(*<*)
(* Auxiliary lemmas about bound comparison *)

lemma [simp]: "\<not> c \<ge>\<^sub>u\<^sub>b None " "\<not> c \<le>\<^sub>l\<^sub>b None"
  by (auto simp add: bound_compare_defs)

lemma neg_bounds_compare:
  "(\<not> (c \<ge>\<^sub>u\<^sub>b b)) \<Longrightarrow> c <\<^sub>u\<^sub>b b" "(\<not> (c \<le>\<^sub>u\<^sub>b b)) \<Longrightarrow> c >\<^sub>u\<^sub>b b" 
  "(\<not> (c >\<^sub>u\<^sub>b b)) \<Longrightarrow> c \<le>\<^sub>u\<^sub>b b" "(\<not> (c <\<^sub>u\<^sub>b b)) \<Longrightarrow> c \<ge>\<^sub>u\<^sub>b b"
  "(\<not> (c \<le>\<^sub>l\<^sub>b b)) \<Longrightarrow> c >\<^sub>l\<^sub>b b" "(\<not> (c \<ge>\<^sub>l\<^sub>b b)) \<Longrightarrow> c <\<^sub>l\<^sub>b b" 
  "(\<not> (c <\<^sub>l\<^sub>b b)) \<Longrightarrow> c \<ge>\<^sub>l\<^sub>b b" "(\<not> (c >\<^sub>l\<^sub>b b)) \<Longrightarrow> c \<le>\<^sub>l\<^sub>b b"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma bounds_compare_contradictory [simp]:
 "\<lbrakk>c \<ge>\<^sub>u\<^sub>b b; c <\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c \<le>\<^sub>u\<^sub>b b; c >\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False"
 "\<lbrakk>c >\<^sub>u\<^sub>b b; c \<le>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c <\<^sub>u\<^sub>b b; c \<ge>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False"
 "\<lbrakk>c \<le>\<^sub>l\<^sub>b b; c >\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c \<ge>\<^sub>l\<^sub>b b; c <\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False" 
 "\<lbrakk>c <\<^sub>l\<^sub>b b; c \<ge>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c >\<^sub>l\<^sub>b b; c \<le>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma compare_strict_nonstrict: 
   "x <\<^sub>u\<^sub>b b \<Longrightarrow> x \<le>\<^sub>u\<^sub>b b"
   "x >\<^sub>u\<^sub>b b \<Longrightarrow> x \<ge>\<^sub>u\<^sub>b b"
   "x <\<^sub>l\<^sub>b b \<Longrightarrow> x \<le>\<^sub>l\<^sub>b b"
   "x >\<^sub>l\<^sub>b b \<Longrightarrow> x \<ge>\<^sub>l\<^sub>b b"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma [simp]: 
   "\<lbrakk> x \<le> c; c <\<^sub>u\<^sub>b b \<rbrakk> \<Longrightarrow> x <\<^sub>u\<^sub>b b" 
   "\<lbrakk> x < c; c \<le>\<^sub>u\<^sub>b b \<rbrakk> \<Longrightarrow> x <\<^sub>u\<^sub>b b"
   "\<lbrakk> x \<le> c; c \<le>\<^sub>u\<^sub>b b \<rbrakk> \<Longrightarrow> x \<le>\<^sub>u\<^sub>b b"
   "\<lbrakk> x \<ge> c; c >\<^sub>l\<^sub>b b \<rbrakk> \<Longrightarrow> x >\<^sub>l\<^sub>b b" 
   "\<lbrakk> x > c; c \<ge>\<^sub>l\<^sub>b b \<rbrakk> \<Longrightarrow> x >\<^sub>l\<^sub>b b"
   "\<lbrakk> x \<ge> c; c \<ge>\<^sub>l\<^sub>b b \<rbrakk> \<Longrightarrow> x \<ge>\<^sub>l\<^sub>b b"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma bounds_lg [simp]: 
  "\<lbrakk> c >\<^sub>u\<^sub>b b; x \<le>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> x < c"
  "\<lbrakk> c \<ge>\<^sub>u\<^sub>b b; x <\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> x < c"
  "\<lbrakk> c \<ge>\<^sub>u\<^sub>b b; x \<le>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> x \<le> c"
  "\<lbrakk> c <\<^sub>l\<^sub>b b; x \<ge>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> x > c"
  "\<lbrakk> c \<le>\<^sub>l\<^sub>b b; x >\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> x > c"
  "\<lbrakk> c \<le>\<^sub>l\<^sub>b b; x \<ge>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> x \<ge> c"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma bounds_compare_Some [simp]: 
  "x \<le>\<^sub>u\<^sub>b Some c \<longleftrightarrow> x \<le> c" "x \<ge>\<^sub>u\<^sub>b Some c \<longleftrightarrow> x \<ge> c"
  "x <\<^sub>u\<^sub>b Some c \<longleftrightarrow> x < c" "x >\<^sub>u\<^sub>b Some c \<longleftrightarrow> x > c"
  "x \<ge>\<^sub>l\<^sub>b Some c \<longleftrightarrow> x \<ge> c" "x \<le>\<^sub>l\<^sub>b Some c \<longleftrightarrow> x \<le> c"
  "x >\<^sub>l\<^sub>b Some c \<longleftrightarrow> x > c" "x <\<^sub>l\<^sub>b Some c \<longleftrightarrow> x < c"
  by (auto simp add: bound_compare_defs)
(*>*)
(*<*)fun in_bounds where
  "in_bounds x v (lb, ub) = (v x \<ge>\<^sub>l\<^sub>b lb x \<and> v x \<le>\<^sub>u\<^sub>b ub x)"
(*>*)
(*<*) fun satisfies_bounds :: "'a::linorder valuation \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>b" 100) where
  "v \<Turnstile>\<^sub>b b \<longleftrightarrow> (\<forall> x. in_bounds x v b)"
declare satisfies_bounds.simps [simp del] 
(*>*)
(*<*)
lemma satisfies_bounds_iff:
 "v \<Turnstile>\<^sub>b (lb, ub) \<equiv> (\<forall> x. v x \<ge>\<^sub>l\<^sub>b lb x \<and> v x \<le>\<^sub>u\<^sub>b ub x)"
by (auto simp add: satisfies_bounds.simps in_bounds.simps)

lemma not_in_bounds:
 "\<not> (in_bounds x v (lb, ub)) = (v x <\<^sub>l\<^sub>b lb x \<or> v x >\<^sub>u\<^sub>b ub x)"
  using bounds_compare_contradictory(7)
  using bounds_compare_contradictory(2)
  using neg_bounds_compare(7)[of "v x" "lb x"]
  using neg_bounds_compare(2)[of "v x" "ub x"]
  by auto
(*>*)
(*<*) fun atoms_equiv_bounds :: "'a::linorder atom set \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> bool" (infixl "\<doteq>" 100) where
  "as \<doteq> (lb, ub) \<longleftrightarrow> (\<forall> v. v \<Turnstile>\<^sub>a\<^sub>s as \<longleftrightarrow> v \<Turnstile>\<^sub>b (lb, ub))"
declare atoms_equiv_bounds.simps [simp del]

lemma atoms_equiv_bounds_simps:
"as \<doteq> (lb, ub) \<equiv> \<forall> v. v \<Turnstile>\<^sub>a\<^sub>s as \<longleftrightarrow> v \<Turnstile>\<^sub>b (lb, ub)"
by (simp add: atoms_equiv_bounds.simps)
(*>*)
text{* A valuation satisfies bounds iff the value of each variable
respects both its lower and upper bound, i.e, @{thm
satisfies_bounds_iff[no_vars]}. Asserted atoms are precisely encoded
by the current bounds in a state (denoted by @{text \<doteq>}) if every 
valuation satisfies them iff it satisfies the bounds, i.e.,
@{thm atoms_equiv_bounds_simps[no_vars, iff]}. *}

text{* The procedure also keeps track of a valuation that is a
candidate solution. Whenever a new atom is asserted, it is checked
whether the valuation is still satisfying. If not, the procedure tries
to fix that by changing it and changing the tableau if necessary (but
so that it remains equivalent to the initial tableau). *}

text{* Therefore, the state of the procedure stores the tableau
(denoted by @{text "\<T>"}), lower and upper bounds (denoted by @{text
"\<B>\<^sub>l"} and @{text "\<B>\<^sub>u"}, and ordered pair of lower and upper bounds
denoted by @{text "\<B>"}), candidate solution (denoted by @{text "\<V>"})
and a flag (denoted by @{text "\<U>"}) indicating if unsatisfiability has
been detected so far: *}

record 'a state = 
  \<T> :: "tableau"   \<B>\<^sub>l :: "'a bounds"   \<B>\<^sub>u :: "'a bounds"   \<V> :: "(var, 'a) mapping"   \<U> :: bool
(*<*)abbreviation Bounds :: "'a state \<Rightarrow> 'a bounds \<times> 'a bounds" ("\<B>") where  "\<B> s \<equiv> (\<B>\<^sub>l s, \<B>\<^sub>u s)"(*>*) 
(*<*) 
definition satisfies_state :: "'a::lrv valuation \<Rightarrow> 'a state \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>s" 100) where "v \<Turnstile>\<^sub>s s \<equiv> v \<Turnstile>\<^sub>b \<B> s \<and> v \<Turnstile>\<^sub>t \<T> s"
(*>*)
(*<*) definition curr_val_satisfies_state :: "'a::lrv state \<Rightarrow> bool" ("\<Turnstile>") where
 "\<Turnstile> s \<equiv> \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>s s"
(*>*)
(*<*)
definition tableau_valuated ("\<nabla>") where
  "\<nabla> s \<equiv> \<forall> x \<in> tvars (\<T> s). Mapping.lookup (\<V> s) x \<noteq> None"
(*>*)

text{* To be a solution of the initial problem, a valuation should
satisfy the initial tableau and list of atoms. Since tableau is
changed only by equivalency preserving transformations and asserted
atoms are encoded in the bounds, a valuation is a solution if it
satisfies both the tableau and the bounds in the final state (when all
atoms have been asserted). So, a valuation @{text v} satisfies a state
@{text s} (denoted by @{text "\<Turnstile>\<^sub>s"}) if it satisfies the tableau and
the bounds, i.e., @{thm satisfies_state_def [no_vars]}. Since @{text
"\<V>"} should be a candidate solution, it should satisfy the state
(unless the @{text \<U>} flag is raised). This is denoted by @{text "\<Turnstile> s"}
and defined by @{thm curr_val_satisfies_state_def[no_vars]}. @{text "\<nabla>
s"} will denote that all variables of @{text "\<T> s"} are explicitly
valuated in @{text "\<V> s"}. *}

(*<*)
definition update\<B> where
  [simp]: "update\<B> field_update x c s = field_update (\<lambda> b. b (x \<mapsto> c)) s"

record 'a Direction = 
  lt :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> bool"
  LB :: "'a state \<Rightarrow> (var \<Rightarrow> 'a option)"
  UB :: "'a state \<Rightarrow> (var \<Rightarrow> 'a option)"
  UB_upd :: "((var \<Rightarrow> 'a option) \<Rightarrow> var \<Rightarrow> 'a option) \<Rightarrow> 'a state \<Rightarrow> 'a state"
  LE :: "var \<Rightarrow> 'a \<Rightarrow> 'a atom"

definition Positive where
  [simp]: "Positive \<equiv> \<lparr> lt = op <, LB = \<B>\<^sub>l, UB = \<B>\<^sub>u, UB_upd = \<B>\<^sub>u_update, LE = Leq \<rparr>"

definition Negative where
  [simp]: "Negative \<equiv> \<lparr> lt = op >, LB = \<B>\<^sub>u, UB = \<B>\<^sub>l, UB_upd = \<B>\<^sub>l_update, LE = Geq \<rparr>"

(*>*)

text{* Assuming that the @{text \<U>} flag and the current valuation
@{text "\<V>"} in the final state determine the solution of a problem, the
@{text assert_all} function can be reduced to the @{text assert_all_state}
function that operates on the states: 
@{text[display] "assert_all t as \<equiv> let s = assert_all_state t as in 
   if (\<U> s) then (False, None) else (True, Some (\<V> s))" } 
*}
text{* Specification for the @{text assert_all_state} can be directly
obtained from the specification of @{text assert_all}, and it describes
the connection between the valuation in the final state and the
initial tableau and atoms. However, we will make an additional
refinement step and give stronger assumptions about the @{text
assert_all_state} function that describes the connection between
the initial tableau and atoms with the tableau and bounds in the final
state. *}

locale AssertAllState = fixes assert_all_state::"tableau \<Rightarrow> 'a::lrv atom list \<Rightarrow> 'a state"
  assumes
  -- {* --- The final and the initial tableau are equivalent. *}
  (*<*)assert_all_state_tableau_equiv:(*>*) "\<triangle> t \<Longrightarrow> let s' = assert_all_state t as in (v::'a valuation) \<Turnstile>\<^sub>t t \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s'" (*<*)and(*>*)

  -- {* --- If @{term \<U>} is not raised, then the valuation in the
final state satisfies its tableau and its bounds (that are, in this
case, equivalent to the set of all asserted bounds). *}
  (*<*)assert_all_state_sat:(*>*) "\<triangle> t \<Longrightarrow> let s' = assert_all_state t as in \<not> \<U> s' \<longrightarrow> \<Turnstile> s'" (*<*)and(*>*)

  (*<*)assert_all_state_sat_atoms_equiv_bounds:(*>*) "\<triangle> t \<Longrightarrow> let s' = assert_all_state t as in \<not> \<U> s' \<longrightarrow> set as \<doteq> \<B> s'" (*<*)and(*>*)

  -- {* --- If @{term \<U>} is raised, then there is no valuation
   satisfying the tableau and the bounds in the final state (that are,
   in this case, equivalent to a subset of asserted atoms). *}
  (*<*)assert_all_state_unsat:(*>*) "\<triangle> t \<Longrightarrow> let s' = assert_all_state t as in \<U> s' \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>s s')"  (*<*)and(*>*)

  (*<*)assert_all_state_unsat_atoms_equiv_bounds:(*>*) "\<triangle> t \<Longrightarrow> let s' = assert_all_state t as in \<U> s' \<longrightarrow> (\<exists> as'. as' \<subseteq> set as \<and> as' \<doteq> \<B> s')"
(*<*) 
begin
definition assert_all where
  "assert_all t as \<equiv> let s = assert_all_state t as in 
     if (\<U> s) then (False, None) else (True, Some (\<V> s))"
end
(*>*)

(*<*)
sublocale AssertAllState < AssertAll assert_all
proof
  fix t as
  assume "\<triangle> t"
  thus "let (sat, v) = assert_all t as in sat \<longrightarrow> \<langle>the v\<rangle> \<Turnstile>\<^sub>t t \<and> \<langle>the v\<rangle> \<Turnstile>\<^sub>a\<^sub>s set as"
    unfolding Let_def assert_all_def
    using assert_all_state_tableau_equiv
    using assert_all_state_sat[of t as]
    using assert_all_state_sat_atoms_equiv_bounds[of t as]
    unfolding atoms_equiv_bounds.simps curr_val_satisfies_state_def satisfies_state_def
    by (auto simp add: Let_def)
next
  fix t as
  assume "\<triangle> t"
  thus "let (sat, v) = assert_all t as in \<not> sat \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s set as)"
    unfolding assert_all_def
    using assert_all_state_tableau_equiv[of t as]
    using assert_all_state_unsat_atoms_equiv_bounds[of t as]
    using assert_all_state_unsat[of t as]
    unfolding atoms_equiv_bounds.simps satisfies_state_def satisfies_atom_set_def
    by (simp add: Let_def) force
qed
(*>*)

text{* The @{text assert_all_state} function can be implemented by first
applying the @{text init} function that creates an initial state based
on the starting tableau, and then by iteratively applying the @{text
assert} function for each atom in the starting atoms list. *}

text{*
\begin{small}
  @{text "assert_loop as s \<equiv> foldl (\<lambda> s' a. if (\<U> s') then s' else assert a s') s as"}
  
  @{text "assert_all_state t as \<equiv> assert_loop ats (init t)"}
\end{small}
*}

(*<*)
locale Init' = 
  fixes init :: "tableau \<Rightarrow> 'a::lrv state"
  assumes (*<*)init'_tableau_normalized:(*>*) "\<triangle> t \<Longrightarrow> \<triangle> (\<T> (init t))"
  assumes (*<*)init'_tableau_equiv:(*>*) "\<triangle> t \<Longrightarrow> (v::'a valuation) \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> (init t)"
  assumes (*<*)init'_sat:(*>*) "\<triangle> t \<Longrightarrow> \<not> \<U> (init t) \<longrightarrow> \<Turnstile> (init t)"
  assumes (*<*)init'_unsat:(*>*) "\<triangle> t \<Longrightarrow> \<U> (init t) \<longrightarrow> (\<forall>v. \<not> v \<Turnstile>\<^sub>s init t)"
  assumes (*<*)init'_atoms_equiv_bounds:(*>*) "\<triangle> t \<Longrightarrow> {} \<doteq> \<B> (init t)"
(*>*)

text{* Specification for @{text "init"} can be obtained from the
specification of @{text asser_all_state} since all its assumptions
must also hold for @{text "init"} (when the list of atoms is
empty). Also, since @{text init} is the first step in the @{text
assert_all_state} implementation, the precondition for @{text init}
the same as for the @{text assert_all_state}. However,
unsatisfiability is never going to be detected during initialization
and @{term \<U>} flag is never going to be raised. Also, the tableau in
the initial state can just be initialized with the starting
tableau. The condition @{term "{} \<doteq> \<B> (init t)"} is equivalent to
asking that initial bounds are empty. Therefore, specification for
@{text "init"} can be refined to: *}

locale Init = fixes init::"tableau \<Rightarrow> 'a::lrv state"
   assumes
  -- {* --- Tableau in the initial state for @{text t} is @{text t}: *} (*<*)init_tableau_id:(*>*) "\<T> (init t) = t" (*<*)and(*>*) 

  -- {* --- Since unsatisfiability is not detected, @{text \<U>}
     flag must not be set: *} (*<*)init_unsat_flag:(*>*) "\<not> \<U> (init t)" (*<*)and(*>*) 

  -- {* --- The current valuation must satisfy the tableau: *} (*<*)init_satisfies_tableau:(*>*) "\<langle>\<V> (init t)\<rangle> \<Turnstile>\<^sub>t t" (*<*)and(*>*) 

  -- {* --- In an inital state no atoms are yet asserted so the bounds
     must be empty: *} 
     (*<*)init_bounds:(*>*) "\<B>\<^sub>l (init t) = (\<lambda> _. None)"   "\<B>\<^sub>u (init t) = (\<lambda> _. None)"  (*<*)and(*>*) 

  -- {* --- All tableau vars are valuated: *} (*<*)init_tableau_valuated:(*>*) "\<nabla> (init t)"
(*<*)
begin
(*>*)
(*<*)
lemma init_satisfies_bounds: 
  "\<langle>\<V> (init t)\<rangle> \<Turnstile>\<^sub>b \<B> (init t)"
  using init_bounds
  unfolding satisfies_bounds.simps in_bounds.simps bound_compare_defs
  by simp

lemma init_satisfies:
  "\<Turnstile> (init t)"
  using init_satisfies_tableau init_satisfies_bounds init_tableau_id
  unfolding curr_val_satisfies_state_def satisfies_state_def
  by simp

lemma init_atoms_equiv_bounds:
 "{} \<doteq> \<B> (init t)"
using init_bounds
unfolding atoms_equiv_bounds.simps satisfies_bounds.simps in_bounds.simps satisfies_atom_set_def
unfolding bound_compare_defs
by simp

lemma init_tableau_normalized:
"\<triangle> t \<Longrightarrow> \<triangle> (\<T> (init t))"
using init_tableau_id
by simp
(*>*)
(*<*)
end
(*>*)
(*<*)
sublocale Init < Init' init
using init_tableau_id init_satisfies init_unsat_flag init_atoms_equiv_bounds
by (unfold_locales) auto
(*>*)

(*<*)
abbreviation vars_list where
 "vars_list t \<equiv> remdups (map lhs t @ (concat (map (AbstractLinearPoly.vars_list \<circ> rhs) t)))"

lemma "tvars t = set (vars_list t)"
by (auto simp add: set_vars_list lvars_def rvars_def)
(*>*)

text{* \smallskip The @{text assert} function asserts a single
atom. Since the @{text init} function does not raise the @{text \<U>}
flag, from the definition of @{text assert_loop}, it is clear that the
flag is not raised when the @{text assert} function is
called. Moreover, the assumptions about the @{text assert_all_state}
imply that the loop invariant must be that if the @{text \<U>} flag is
not raised, then the current valuation must satisfy the state (i.e.,
@{text "\<Turnstile> s"}). The @{text assert} function will be more easily
implemented if it is always applied to a state with a normalized and
valuated tableau, so we make this another loop invariant. Therefore,
the precondition for the @{text "assert a s"} function call is that
@{text "\<not> \<U> s"}, @{text "\<Turnstile> s"}, @{text "\<triangle> (\<T> s)"} and @{text "\<nabla> s"}
hold. The specification for @{text "assert"} directly follows from the
specification of @{text assert_all_state} (except that it is
additionally required that bounds reflect asserted atoms also when
unsatisfiability is detected, and that it is required that @{text
assert} keeps the tableau normalized and valuated). *}

locale Assert = fixes assert::"'a::lrv atom \<Rightarrow> 'a state \<Rightarrow> 'a state"
  assumes
 -- {* --- Tableau remains equivalent to the previous one and normalized and valuated. *}
  (*<*)assert_tableau:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> let s' = assert a s in
     ((v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') \<and> \<nabla> s'" (*<*)and(*>*)

  -- {* --- If the @{term \<U>} flag is not raised, then the current
   valuation is updated so that it satisfies the current tableau and
   the current bounds. *}
  (*<*)assert_sat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<not> \<U> (assert a s) \<longrightarrow> \<Turnstile> (assert a s)" (*<*)and(*>*)

 -- {* --- The set of asserted atoms remains equivalent to the bounds
    in the state. *}
  (*<*)assert_atoms_equiv_bounds:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> (assert a s)" (*<*)and(*>*)

  -- {* --- If the @{term \<U>} flag is raised, then there is no valuation
   that satisfies both the current tableau and the current bounds. *}
  (*<*)assert_unsat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<U> (assert a s) \<longrightarrow>  \<not> (\<exists> v. v \<Turnstile>\<^sub>s (assert a s))"
(*<*)
begin
lemma assert_tableau_equiv: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> (v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (assert a s)"
using assert_tableau
by (simp add: Let_def)

lemma assert_tableau_normalized: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<triangle> (\<T> (assert a s))"
using assert_tableau
by (simp add: Let_def)

lemma assert_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (assert a s)"
using assert_tableau
by (simp add: Let_def)
end
(*>*)

(*<*)
locale AssertAllState' = Init init + Assert assert for
  init :: "tableau \<Rightarrow> 'a::lrv state" and assert :: "'a atom \<Rightarrow> 'a state \<Rightarrow> 'a state"
begin
(*>*)
(*<*) definition assert_loop where
  "assert_loop as s \<equiv> foldl (\<lambda> s' a. if (\<U> s') then s' else assert a s') s as"
(*>*)
(*<*) definition assert_all_state where [simp]:
  "assert_all_state t as \<equiv> assert_loop as (init t)"
(*>*)
(*<*)
lemma AssertAllState'_precond: 
  "\<triangle> t \<Longrightarrow> \<triangle> (\<T> (assert_all_state t as)) \<and> (\<nabla> (assert_all_state t as)) \<and> (\<not> \<U> (assert_all_state t as) \<longrightarrow> \<Turnstile> (assert_all_state t as))"
  unfolding assert_all_state_def assert_loop_def
  using init_satisfies init_tableau_normalized
  using assert_sat assert_tableau_normalized init_tableau_valuated assert_tableau_valuated
  by (induct as rule: rev_induct) auto

lemma AssertAllState'Induct:
  assumes 
  "\<triangle> t"
  "P (init t)"
  "\<And> s a. \<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s; P s\<rbrakk> \<Longrightarrow> P (assert a s)"
  shows "P (assert_all_state t as)"
proof (induct as rule: rev_induct)
  case Nil
  thus ?case
    unfolding assert_all_state_def assert_loop_def
    using assms(2)
    by simp
next
  case (snoc a as')
  let ?f = "\<lambda>s' a. if \<U> s' then s' else assert a s'"
  let ?s = "foldl ?f (init t) as'"
  show ?case
  proof (cases "\<U> ?s")
    case True
    thus ?thesis
      using snoc
      unfolding assert_all_state_def assert_loop_def
      by simp
  next
    case False
    thus ?thesis
      using snoc
      using assms(1) assms(3)
      using AssertAllState'_precond
      unfolding assert_all_state_def assert_loop_def
      by auto
  qed
qed

lemma AssertAllState'_sat_atoms_equiv_bounds:
   "\<triangle> t \<Longrightarrow> \<not> \<U> (assert_all_state t as) \<longrightarrow> set as \<doteq> \<B> (assert_all_state t as)"
  using AssertAllState'_precond
  using init_atoms_equiv_bounds assert_atoms_equiv_bounds
  unfolding assert_all_state_def assert_loop_def
  by (induct as rule: rev_induct) auto

lemma AssertAllState'_unsat_atoms_equiv_bounds:
  assumes "\<triangle> t"
  shows "\<U> (assert_all_state t as) \<longrightarrow>
          (\<exists>as'\<subseteq>set as. as' \<doteq> \<B> (assert_all_state t as))"
proof (induct as rule: rev_induct)
  case Nil
  thus ?case
    using assms init_atoms_equiv_bounds
    unfolding assert_all_state_def assert_loop_def
    by simp
next
  case (snoc a as')
  let ?f = "\<lambda>s' a. if \<U> s' then s' else assert a s'"
  let ?s = "foldl ?f (init t) as'"
  show ?case
  proof (cases "\<U> ?s")
    case True
    thus ?thesis
      using snoc
      unfolding assert_all_state_def assert_loop_def
      by auto
  next
    case False
    thus ?thesis
      using assms AssertAllState'_precond[of t as']
      using AssertAllState'_sat_atoms_equiv_bounds[of t as']
      using assert_atoms_equiv_bounds
      unfolding assert_all_state_def assert_loop_def
      by auto
  qed
qed

(*>*)
(*<*)
end
(*>*)
text{* Under these assumptions, it can easily be shown (mainly by
induction) that the previously shown implementation of @{text
"assert_all_state"} satisfies its specification.*}
(*<*)
sublocale AssertAllState' < AssertAllState assert_all_state
proof
  fix v::"'a valuation" and t as
  assume *: "\<triangle> t"

  show "let s' = assert_all_state t as in v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> s'"
    using  init_tableau_id[of t] assert_tableau_equiv[of _ v]
    by (induct rule: AssertAllState'Induct) (auto simp add: * )

  show "let s' = assert_all_state t as in \<not> \<U> s' \<longrightarrow> \<Turnstile> s'"
    using AssertAllState'_precond
    by (simp add: * )

  show "let s' = assert_all_state t as in \<not> \<U> s' \<longrightarrow> set as \<doteq> \<B> s'"
    using *
    unfolding Let_def
    by (rule AssertAllState'_sat_atoms_equiv_bounds)

  show "let s' = assert_all_state t as in \<U> s' \<longrightarrow>
          (\<exists>as'\<subseteq>set as. as' \<doteq> \<B> s')"
    using *
    unfolding Let_def
    by (rule AssertAllState'_unsat_atoms_equiv_bounds)

  show "let s' = assert_all_state t as in \<U> s' \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s s')"
    using init_unsat_flag assert_unsat
    by (induct rule: AssertAllState'Induct) (auto simp add: * )
qed
(*>*)

subsection{* Aserting Single Atoms *}

text{* The @{term assert} function is split in two phases. First,
@{term assert_bound} updates the bounds and checks only for conflicts
cheap to detect. Next, @{text check} performs the full simplex
algorithm. The @{text assert} function can be implemented as @{text
"assert a s = check (assert_bound a s)"}. Note that it is also
possible to do the first phase for several asserted atoms, and only
then to let the expensive second phase work.

\medskip Asserting an atom @{text "x \<bowtie> b"} begins with the function
@{text assert_bound}.  If the atom is subsumed by the current bounds,
then no changes are performed. Otherwise, bounds for @{text "x"} are
changed to incorporate the atom. If the atom is inconsistent with the
previous bounds for @{text "x"}, the @{term \<U>} flag is raised. If
@{text "x"} is not a lhs variable in the current tableau and if the
value for @{text "x"} in the current valuation violates the new bound
@{text "b"}, the value for @{text "x"} can be updated and set to
@{text "b"}, meanwhile updating the values for lhs variables of
the tableau so that it remains satisfied. Otherwise, no changes to the
current valuation are performed. *} 
(*<*)
fun satisfies_bounds_set  :: "'a::linorder valuation \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> var set \<Rightarrow> bool" where
"satisfies_bounds_set v (lb, ub) S \<longleftrightarrow> (\<forall> x \<in> S. in_bounds x v (lb, ub))"
declare satisfies_bounds_set.simps [simp del]
syntax
  "_satisfies_bounds_set" :: "(var \<Rightarrow> 'a::linorder) \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> var set \<Rightarrow> bool"    ("_ \<Turnstile>\<^sub>b _ \<parallel>/ _")
translations
  "v \<Turnstile>\<^sub>b b \<parallel> S" == "CONST satisfies_bounds_set v b S"
lemma satisfies_bounds_set_iff:
"v \<Turnstile>\<^sub>b (lb, ub) \<parallel> S \<equiv> (\<forall> x \<in> S. v x \<ge>\<^sub>l\<^sub>b lb x \<and> v x \<le>\<^sub>u\<^sub>b ub x)"
by (simp add: satisfies_bounds_set.simps)
(*>*)
(*<*)
definition curr_val_satisfies_no_lhs ("\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s") where
"\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<equiv> \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t (\<T> s) \<and> (\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>b (\<B> s) \<parallel> (- lvars (\<T> s)))"
lemma satisfies_satisfies_no_lhs:
"\<Turnstile> s \<Longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
by (simp add: curr_val_satisfies_state_def satisfies_state_def curr_val_satisfies_no_lhs_def satisfies_bounds.simps satisfies_bounds_set.simps)
(*>*)
(*<*)
definition bounds_consistent :: "'a::linorder state \<Rightarrow> bool" ("\<diamond>") where
"\<diamond> s \<equiv> 
   \<forall> x. if \<B>\<^sub>l s x = None \<or> \<B>\<^sub>u s x = None then True else the (\<B>\<^sub>l s x) \<le> the (\<B>\<^sub>u s x)"
(*>*)

text{* So, the @{text assert_bound} function must ensure that the
given atom is included in the bounds, that the tableau remains
satisfied by the valuation and that all variables except the lhs variables 
in the tableau are within their
bounds. To formalize this, we introduce the notation @{text "v
\<Turnstile>\<^sub>b (lb, ub) \<parallel> S"}, and define @{thm
satisfies_bounds_set_iff[no_vars]}, and @{thm
curr_val_satisfies_no_lhs_def[no_vars]}. The @{text assert_bound}
function raises the @{text \<U>} flag if and only if lower and upper
bounds overlap. This is formalized as @{thm
bounds_consistent_def[no_vars]}. *}

(*<*)
lemma satisfies_bounds_consistent:
  "(v::'a::linorder valuation) \<Turnstile>\<^sub>b \<B> s \<longrightarrow> \<diamond> s"
  unfolding satisfies_bounds.simps in_bounds.simps bounds_consistent_def bound_compare_defs
  by (auto split: option.split) force

lemma satisfies_consistent:
  "\<Turnstile> s \<longrightarrow> \<diamond> s"
by (auto simp add: curr_val_satisfies_state_def satisfies_state_def satisfies_bounds_consistent)

lemma bounds_consistent_geq_lb: 
  "\<lbrakk>\<diamond> s; \<B>\<^sub>u s x\<^sub>i = Some c\<rbrakk>
    \<Longrightarrow> c \<ge>\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i"
  unfolding bounds_consistent_def
  by (cases "\<B>\<^sub>l s x\<^sub>i", auto simp add: bound_compare_defs split: if_splits)
     (erule_tac x="x\<^sub>i" in allE, auto)

lemma bounds_consistent_leq_ub: 
  "\<lbrakk>\<diamond> s; \<B>\<^sub>l s x\<^sub>i = Some c\<rbrakk>
    \<Longrightarrow> c \<le>\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i"
  unfolding bounds_consistent_def
  by (cases "\<B>\<^sub>u s x\<^sub>i", auto simp add: bound_compare_defs split: if_splits)
     (erule_tac x="x\<^sub>i" in allE, auto)

lemma bounds_consistent_gt_ub:
  "\<lbrakk>\<diamond> s; c <\<^sub>l\<^sub>b \<B>\<^sub>l s x \<rbrakk> \<Longrightarrow> \<not> c >\<^sub>u\<^sub>b \<B>\<^sub>u s x"
  unfolding bounds_consistent_def
  by (case_tac[!] "\<B>\<^sub>l s x", case_tac[!] "\<B>\<^sub>u s x")
     (auto simp add: bound_compare_defs, erule_tac x="x" in allE, simp)

lemma bounds_consistent_lt_lb:
  "\<lbrakk>\<diamond> s; c >\<^sub>u\<^sub>b \<B>\<^sub>u s x \<rbrakk> \<Longrightarrow> \<not> c <\<^sub>l\<^sub>b \<B>\<^sub>l s x"
  unfolding bounds_consistent_def
  by (case_tac[!] "\<B>\<^sub>l s x", case_tac[!] "\<B>\<^sub>u s x")
     (auto simp add: bound_compare_defs, erule_tac x="x" in allE, simp)
(*>*)

text{* Since the @{text assert_bound} is the first step in the @{text
assert} function implementation, the preconditions for @{text
assert_bound} are the same as preconditions for the @{text assert}
function. The specifiction for the @{text assert_bound} is:*}

locale AssertBound = fixes assert_bound::"'a::lrv atom \<Rightarrow> 'a state \<Rightarrow> 'a state"
  assumes
  -- {* --- The tableau remains unchanged and valuated. *}

(*<*)assert_bound_tableau:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> let s' = assert_bound a s in \<T> s' = \<T> s \<and> \<nabla> s'" (*<*)and(*>*)

  -- {* --- If the @{term \<U>} flag is not set, all but the
   lhs variables in the tableau remain within their bounds,
   the new valuation satisfies the tableau, and bounds do not overlap.*}
(*<*)assert_bound_sat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> 
     let s' = assert_bound a s in \<not> \<U> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<and> \<diamond> s'" (*<*)and(*>*)

  -- {* --- The set of asserted atoms remains equivalent to the bounds in the state. *}

(*<*)assert_bound_atoms_equiv_bounds:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> (assert_bound a s)" (*<*)and(*>*)

  -- {* --- @{term \<U>} flag is raised, only if the bounds became inconsistent:*}

(*<*)assert_bound_unsat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> let s' = assert_bound a s in \<U> s' \<longrightarrow> \<not>(\<exists>v. v \<Turnstile>\<^sub>s s')"
(*<*)
begin
lemma assert_bound_tableau_id: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<T> (assert_bound a s) = \<T> s"
using assert_bound_tableau
by (simp add: Let_def)

lemma assert_bound_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (assert_bound a s)"
using assert_bound_tableau
by (simp add: Let_def)

end
(*>*)
(*<*)
locale AssertBoundNoLhs = 
  fixes assert_bound :: "'a::lrv atom \<Rightarrow> 'a state \<Rightarrow> 'a state"
  assumes (*<*)assert_bound_nolhs_tableau_id:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow> \<T> (assert_bound a s) = \<T> s"
  assumes (*<*)assert_bound_nolhs_sat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow> 
    \<not> \<U> (assert_bound a s) \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound a s) \<and> \<diamond> (assert_bound a s)"
  assumes (*<*)assert_bound_nolhs_atoms_equiv_bounds:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow> 
    ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> (assert_bound a s)"
  assumes (*<*)assert_bound_nolhs_unsat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow> 
    \<U> (assert_bound a s) \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>s assert_bound a s)"
  assumes (*<*)assert_bound_nolhs_tableau_valuated:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow> 
   \<nabla> (assert_bound a s)"
(*>*)
(*<*)
sublocale AssertBoundNoLhs < AssertBound
  using satisfies_satisfies_no_lhs satisfies_consistent
  using assert_bound_nolhs_tableau_id assert_bound_nolhs_sat assert_bound_nolhs_atoms_equiv_bounds assert_bound_nolhs_unsat assert_bound_nolhs_tableau_valuated
  by (unfold_locales) (auto simp add: Let_def)
(*>*)

text{* The second phase of @{text assert}, the @{text check} function,
is the heart of the Simplex algorithm. It is always called after
@{text assert_bound}, but in two different situations. In the first
case @{text assert_bound} raised the @{text \<U>} flag and then
@{text check} should retain the flag and should not perform any changes. 
In the second case @{text assert_bound} did not raise the
@{text \<U>} flag, so @{text "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"}, @{text "\<diamond> s"}, @{text "\<triangle> (\<T>
s)"}, and @{text "\<nabla> s"} hold. *}

locale Check = fixes check::"'a::lrv state \<Rightarrow> 'a state"
  assumes
  -- {* --- If @{text check} is called from an inconsistent state, the state is unchanged. *}

(*<*)check_unsat_id:(*>*) "\<lbrakk> \<U> s \<rbrakk> \<Longrightarrow> check s = s"  (*<*)and(*>*)

  -- {* --- The tableau remains equivalent to the previous one, normalized and valuated. *}

(*<*)check_tableau: (*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> 
   let s' = check s in ((v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') \<and> \<nabla> s'" (*<*)and(*>*)

  -- {* --- The bounds remain unchanged. *}

(*<*)check_bounds_id: (*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<B> (check s) = \<B> s"  (*<*)and(*>*)

  -- {* --- If @{term \<U>} flag is not raised, the current valuation
   @{text "\<V>"} satisfies both the tableau and the bounds and if it is
   raised, there is no valuation that satisfies them. *}

(*<*)check_sat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<not> \<U> (check s) \<longrightarrow> \<Turnstile> (check s)"  (*<*)and(*>*)


(*<*)check_unsat:(*>*) "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<U> (check s) \<longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>s (check s))"
(*<*)
begin
lemma check_tableau_equiv: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow>
                      (v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (check s)" 
using check_tableau
by (simp add: Let_def)


lemma check_tableau_normalized: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<triangle> (\<T> (check s))"
using check_tableau
by (simp add: Let_def)

lemma check_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (check s)"
using check_tableau
by (simp add: Let_def)
end
(*>*)
(*<*)
locale Assert' = AssertBound assert_bound + Check check for
  assert_bound :: "'a::lrv atom \<Rightarrow> 'a state \<Rightarrow> 'a state" and
  check :: "'a::lrv state \<Rightarrow> 'a state"
begin
definition assert :: "'a atom \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "assert a s \<equiv> check (assert_bound a s)"

lemma Assert'Precond: 
  assumes "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  shows "\<triangle> (\<T> (assert_bound a s))" "\<not> \<U> (assert_bound a s) \<longrightarrow>  \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound a s) \<and> \<diamond> (assert_bound a s)" "\<nabla> (assert_bound a s)"
using assms
using assert_bound_tableau_id assert_bound_sat assert_bound_tableau_valuated
by (auto simp add: satisfies_bounds_consistent Let_def)
end
(*>*)
(*<*)
sublocale Assert' < Assert assert
proof
  fix s::"'a state" and v::"'a valuation" and  a::"'a atom"
  assume *: "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  have "\<triangle> (\<T> (assert a s))"
    using check_tableau_normalized[of "assert_bound a s"] check_unsat_id[of "assert_bound a s"] *
    using assert_bound_sat[of s a] Assert'Precond[of s a]
    by (force simp add: assert_def)
  moreover
  have "v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> (assert a s)"
    using check_tableau_equiv[of "assert_bound a s" v] *
    using check_unsat_id[of "assert_bound a s"]
    by (force simp add: assert_def Assert'Precond assert_bound_sat assert_bound_tableau_id)
  moreover
  have "\<nabla> (assert a s)"
    using assert_bound_tableau_valuated[of s a] *
    using check_tableau_valuated[of "assert_bound a s"]
    using check_unsat_id[of "assert_bound a s"]
    by (cases "\<U> (assert_bound a s)") (auto simp add: Assert'Precond assert_def)
  ultimately
  show "let s' = assert a s in (v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') \<and> \<nabla> s'"
    by (simp add: Let_def)
next
  fix s::"'a state" and a::"'a atom"
  assume "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  thus "\<not> \<U> (assert a s) \<longrightarrow> \<Turnstile> (assert a s)"
    unfolding assert_def
    using check_unsat_id[of "assert_bound a s"]
    using check_sat[of "assert_bound a s"]
    by (force simp add: Assert'Precond)
next
  fix s::"'a state" and a::"'a atom" and ats::"'a atom set"
  assume "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  thus "ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> (assert a s)"
    using assert_bound_atoms_equiv_bounds[of s ats a]
    using check_unsat_id[of "assert_bound a s"] check_bounds_id
    by (cases "\<U> (assert_bound a s)") (auto simp add: Assert'Precond assert_def)
next
  fix s::"'a state" and a::"'a atom"
  assume *: "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  show "\<U> (assert a s) \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s assert a s)"
  proof (cases "\<U> (assert_bound a s)")
    case True
    thus ?thesis
      unfolding assert_def
      using * assert_bound_unsat check_tableau_equiv[of "assert_bound a s"] check_bounds_id 
      using check_unsat_id[of "assert_bound a s"]
      by (auto simp add: Assert'Precond satisfies_state_def Let_def)
  next
    case False
    thus ?thesis
      unfolding assert_def
      using * assert_bound_sat[of s a] check_unsat
      by (auto simp add: Assert'Precond)
  qed
qed
(*>*)
text{* Under these assumptions for @{text "assert_bound"} and @{text
"check"}, it can be easily shown that the implementation of @{text
"assert"} (previously given) satisfies its specification. *}
(*<*)
locale AssertAllState'' = Init init + AssertBoundNoLhs assert_bound + Check check for
  init :: "tableau \<Rightarrow> 'a::lrv state" and
  assert_bound :: "'a::lrv atom \<Rightarrow> 'a state \<Rightarrow> 'a state" and
  check :: "'a::lrv state \<Rightarrow> 'a state"
begin
definition assert_bound_loop where
  "assert_bound_loop ats s \<equiv> foldl (\<lambda> s' a. if (\<U> s') then s' else assert_bound a s') s ats"
definition assert_all_state where [simp]:
  "assert_all_state t ats \<equiv> check (assert_bound_loop ats (init t))"
(*>*)
text{* However, for efficiency reasons, we want to allow
implementations that delay the @{text check} function call and call it
after several @{text assert_bound} calls. For example:

\smallskip
\begin{small}
@{thm assert_bound_loop_def[no_vars]}

@{thm assert_all_state_def[no_vars]}
\end{small}
\smallskip

Then, the loop consists only of @{text assert_bound} calls, so @{text
assert_bound} postcondition must imply its precondition. This is not
the case, since variables on the lhs may be out of their
bounds. Therefore, we make a refinement and specify weaker
preconditions (replace @{text "\<Turnstile> s"}, by @{text
"\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"} and @{text
"\<diamond> s"}) for @{text assert_bound}, and show that these
preconditions are still good enough to prove the correctnes of this
alternative @{text assert_all_state} definition. *}

(*<*)
lemma AssertAllState''_precond':
  assumes "\<triangle> (\<T> s)" "\<nabla> s" "\<not> \<U> s \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> \<diamond> s"
  shows "let s' = assert_bound_loop ats s in
         \<triangle> (\<T> s') \<and> \<nabla> s' \<and> (\<not> \<U> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<and> \<diamond> s')"
using assms
using assert_bound_nolhs_tableau_id assert_bound_nolhs_sat assert_bound_nolhs_tableau_valuated
by (induct ats rule: rev_induct) (auto simp add: assert_bound_loop_def Let_def)

lemma AssertAllState''_precond:
  assumes "\<triangle> t"
  shows "let s' = assert_bound_loop ats (init t) in
         \<triangle> (\<T> s') \<and> \<nabla> s' \<and> (\<not> \<U> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<and> \<diamond> s')"
using assms
using AssertAllState''_precond'[of "init t" ats]
by (simp add: Let_def init_tableau_id init_unsat_flag init_satisfies satisfies_consistent satisfies_satisfies_no_lhs init_tableau_valuated)

lemma AssertAllState''Induct:
  assumes 
  "\<triangle> t"
  "P (init t)"
  "\<And> s a. \<lbrakk>\<not> \<U> s;  \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s; P s\<rbrakk> \<Longrightarrow> P (assert_bound a s)"
  shows "P (assert_bound_loop ats (init t))"
proof (induct ats rule: rev_induct)
  case Nil
  thus ?case
    unfolding assert_bound_loop_def
    using assms(2)
    by simp
next
  case (snoc a ats')
  let ?f = "\<lambda>s' a. if \<U> s' then s' else assert_bound a s'"
  let ?s = "foldl ?f (init t) ats'"
  show ?case
  proof (cases "\<U> ?s")
    case True
    thus ?thesis
      using snoc
      unfolding  assert_bound_loop_def
      by simp
  next
    case False
    thus ?thesis
      using snoc
      using assms(1) assms(3)
      using AssertAllState''_precond
      by (simp add: assert_bound_loop_def Let_def curr_val_satisfies_no_lhs_def)
  qed
qed

lemma AssertAllState''_tableau_id:
 "\<triangle> t \<Longrightarrow> \<T> (assert_bound_loop ats (init t)) = \<T> (init t)"
  by (rule AssertAllState''Induct) (auto simp add: init_tableau_id assert_bound_nolhs_tableau_id)

lemma AssertAllState''_sat: 
  "\<triangle> t \<Longrightarrow> 
    \<not> \<U> (assert_bound_loop ats (init t)) \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound_loop ats (init t)) \<and> \<diamond> (assert_bound_loop ats (init t))"
  by (rule AssertAllState''Induct) (auto simp add: init_unsat_flag init_satisfies satisfies_consistent satisfies_satisfies_no_lhs assert_bound_nolhs_sat)

lemma AssertAllState''_unsat:
 "\<triangle> t \<Longrightarrow> \<U> (assert_bound_loop ats (init t)) \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s assert_bound_loop ats (init t))"
  by (rule AssertAllState''Induct) (auto simp add: init_tableau_id assert_bound_nolhs_unsat init_unsat_flag)

lemma AssertAllState''_sat_atoms_equiv_bounds:
  "\<triangle> t \<Longrightarrow> \<not> \<U> (assert_bound_loop ats (init t)) \<longrightarrow> set ats \<doteq> \<B> (assert_bound_loop ats (init t))"
  using AssertAllState''_precond
  using assert_bound_nolhs_atoms_equiv_bounds init_atoms_equiv_bounds
  by (induct ats rule: rev_induct) (auto simp add: Let_def assert_bound_loop_def)

lemma AssertAllState''_unsat_atoms_equiv_bounds: 
  assumes "\<triangle> t"
  shows "\<U> (assert_bound_loop ats (init t)) \<longrightarrow> (\<exists>ats'\<subseteq>set ats. ats' \<doteq> \<B> (assert_bound_loop ats (init t)))"
proof (induct ats rule: rev_induct)
  case Nil
  thus ?case
    unfolding assert_bound_loop_def
    using init_atoms_equiv_bounds assms
    by simp
next
  case (snoc a ats')
  let ?f = "\<lambda>s' a. if \<U> s' then s' else assert_bound a s'"
  let ?s = "foldl ?f (init t) ats'"
  show ?case
  proof (cases "\<U> ?s")
    case True
    thus ?thesis
      using snoc
      unfolding assert_bound_loop_def
      by auto
  next
    case False
    thus ?thesis
      using assms AssertAllState''_precond[of t ats']
      using assert_bound_nolhs_atoms_equiv_bounds
      using AssertAllState''_sat_atoms_equiv_bounds[of t ats']
      by (auto simp add: assert_bound_loop_def Let_def)
  qed
qed

end

sublocale AssertAllState'' < AssertAllState assert_all_state
proof
  fix v::"'a valuation" and t ats
  assume *: "\<triangle> t"
  show "let s' = assert_all_state t ats in v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> s'"
    unfolding assert_all_state_def
    using * check_tableau_equiv[of "assert_bound_loop ats (init t)" v] AssertAllState''_tableau_id[of t ats] init_tableau_id[of t]
    using AssertAllState''_sat[of t ats] check_unsat_id[of "assert_bound_loop ats (init t)"]
    using AssertAllState''_precond[of t ats]
    by force

  show "let s' = assert_all_state t ats in \<not> \<U> s' \<longrightarrow> \<Turnstile> s'"
    unfolding assert_all_state_def
    using * AssertAllState''_precond[of t ats]
    using check_sat check_unsat_id
    by (force simp add: Let_def)

  show "let s' = assert_all_state t ats in \<U> s' \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s s')"
    using * check_unsat check_unsat_id[of "assert_bound_loop ats (init t)"] check_bounds_id
    using AssertAllState''_unsat[of t ats] AssertAllState''_precond[of t ats]
    by (force simp add: Let_def satisfies_state_def)

  show "let s' = assert_all_state t ats in \<not> \<U> s' \<longrightarrow> set ats \<doteq> \<B> s'"
    unfolding assert_all_state_def
    using * AssertAllState''_precond[of t ats]
    using check_bounds_id[of "assert_bound_loop ats (init t)"] check_unsat_id[of "assert_bound_loop ats (init t)"]
    using AssertAllState''_sat_atoms_equiv_bounds[of t ats]
    by (force simp add: Let_def assert_all_state_def)

  show "let s' = assert_all_state t ats in \<U> s' \<longrightarrow>
       (\<exists>ats'\<subseteq>set ats. ats' \<doteq> \<B> s')"
    unfolding assert_all_state_def
    using * AssertAllState''_precond[of t ats]
    unfolding Let_def
    using check_bounds_id[of "assert_bound_loop ats (init t)"]
    using AssertAllState''_unsat_atoms_equiv_bounds[of t ats]
    using AssertAllState''_sat_atoms_equiv_bounds[of t ats]
    using check_unsat_id[of "assert_bound_loop ats (init t)"]
    by (cases "\<U> (assert_bound_loop ats (init t))") (auto simp add: Let_def)
qed
(*>*)

subsection{* Update and Pivot *}

text{* Both @{text "assert_bound"} and @{text "check"} need to update
the valuation so that the tableau remains satisfied. If the value for
a variable not on the lhs of the tableau is changed, this
can be done rather easily (once the value of that variable is changed,
one should recalculate and change the values for all lhs
variables of the tableau). The @{text update} function does this, and
it is specified by: *}

locale Update = fixes update::"var \<Rightarrow> 'a::lrv \<Rightarrow> 'a state \<Rightarrow> 'a state"
  assumes 
  -- {* --- Tableau, bounds, and the unsatisfiability flag are preserved. *} 

(*<*)update_id: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> 
     let s' = update x c s in \<T> s' = \<T> s \<and> \<B> s' = \<B> s \<and> \<U> s' = \<U> s" (*<*)and(*>*)

  -- {* --- Tableau remains valuated. *}

(*<*)update_tableau_valuated: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<nabla> (update x v s)"  (*<*)and(*>*)

  -- {* --- The given variable @{text "x"} in the updated valuation is
   set to the given value @{text "v"} while all other variables
   (except those on the lhs of the tableau) are
   unchanged. *}

(*<*)update_valuation_nonlhs: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> x' \<notin> lvars (\<T> s) \<longrightarrow> 
       look (\<V> (update x v s)) x' = (if x = x' then Some v else look (\<V> s) x')" (*<*)and(*>*)

  -- {* --- Updated valuation continues to satisfy the tableau. *}

(*<*)update_satisfies_tableau: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow>  \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<longrightarrow> \<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>t \<T> s"
(*<*)
begin
lemma update_bounds_id:
"\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow>  \<B>\<^sub>u (update x c s) = \<B>\<^sub>u s \<and> \<B>\<^sub>l (update x c s) = \<B>\<^sub>l s"
  using update_id
  by (auto simp add: Let_def)

lemma update_tableau_id: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<T> (update x c s) = \<T> s"
  using update_id
  by (auto simp add: Let_def)

lemma update_unsat_id: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<U> (update x c s) = \<U> s"
  using update_id
  by (auto simp add: Let_def)

definition assert_bound' where
 [simp]: "assert_bound' dir x c s \<equiv> 
       (if (\<unrhd>\<^sub>u\<^sub>b (lt dir)) c (UB dir s x) then s
          else let s' = update\<B> (UB_upd dir) x c s in
             if (\<lhd>\<^sub>l\<^sub>b (lt dir)) c ((LB dir) s x) then 
                  s' \<lparr> \<U> := True \<rparr> 
             else if x \<notin> lvars (\<T> s') \<and> (lt dir) c (\<langle>\<V> s\<rangle> x) then 
                  update x c s'
             else 
                  s')
  "

primrec assert_bound :: "'a::lrv atom \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "assert_bound (Leq x c) s = assert_bound' Positive x c s"
| "assert_bound (Geq x c) s = assert_bound' Negative x c s"

lemma assert_bound'_cases:
  assumes "\<lbrakk>\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)\<rbrakk> \<Longrightarrow> P s"
  assumes "\<lbrakk>\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)\<rbrakk> \<Longrightarrow> 
     P ((update\<B> (UB_upd dir) x c s) \<lparr> \<U> := True \<rparr>)"
  assumes "\<lbrakk>x \<notin> lvars (\<T> s); (lt dir) c (\<langle>\<V> s\<rangle> x); \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x))\<rbrakk> \<Longrightarrow>  P (update x c ((update\<B> (UB_upd dir) x c s)))"
  assumes "\<lbrakk>\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)); x \<in> lvars (\<T> s)\<rbrakk> \<Longrightarrow> 
     P ((update\<B> (UB_upd dir) x c s))"
  assumes "\<lbrakk>\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)); \<not> ((lt dir) c (\<langle>\<V> s\<rangle> x))\<rbrakk> \<Longrightarrow> 
     P ((update\<B> (UB_upd dir) x c s))"
  assumes "dir = Positive \<or> dir = Negative"
  shows "P (assert_bound' dir x c s)"
proof (cases "\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)")
  case True
  thus ?thesis
    using assms(1)
    by simp
next
  case False
  show ?thesis
  proof (cases "\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)")
    case True
    thus ?thesis
      using `\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)`
      using assms(2)
      by simp
  next
    case False
    show ?thesis
    proof (cases "x \<notin> lvars (\<T> (update\<B> (UB_upd dir) x c s)) \<and> (lt dir) c (\<langle>\<V> s\<rangle> x)")
      case True
      thus ?thesis
        using `\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)` `\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)`
        using assms(3) assms(6)
        by auto
    next
      case False
      hence "x \<in> lvars (\<T> (update\<B> (UB_upd dir) x c s)) \<or> \<not> ((lt dir) c (\<langle>\<V> s\<rangle> x))"
        by simp
      thus ?thesis
      proof
        assume "x \<in> lvars (\<T> (update\<B> (UB_upd dir) x c s))"
        thus ?thesis
          using `\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)` `\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)`
          using assms(4) assms(6)
          by auto
      next
        assume "\<not> (lt dir) c (\<langle>\<V> s\<rangle> x)"
        thus ?thesis
          using `\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)` `\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)`
          using assms(5) assms(6)
          by simp
      qed
    qed
  qed
qed

lemma assert_bound_cases:
  assumes "\<And> c x dir.
     \<lbrakk> dir = Positive \<or> dir = Negative; 
       a = LE dir x c; 
       \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)
     \<rbrakk> \<Longrightarrow> 
       P' (lt dir) (UB dir) (LB dir) (UB_upd dir) s"
  assumes "\<And> c x dir. 
     \<lbrakk>dir = Positive \<or> dir = Negative; 
      a = LE dir x c;
      \<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x); \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)
     \<rbrakk> \<Longrightarrow> 
        P' (lt dir) (UB dir) (LB dir) (UB_upd dir) ((update\<B> (UB_upd dir) x c s)\<lparr>\<U> := True\<rparr>)"
  assumes "\<And> c x dir. 
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       x \<notin> lvars (\<T> s); (lt dir) c (\<langle>\<V> s\<rangle> x); 
      \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x))
     \<rbrakk> \<Longrightarrow>  
        P' (lt dir) (UB dir) (LB dir) (UB_upd dir) (update x c ((update\<B> (UB_upd dir) x c s)))"
  assumes "\<And> c x dir. 
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       x \<in> lvars (\<T> s); \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x));
       \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x))
     \<rbrakk> \<Longrightarrow> 
        P' (lt dir) (UB dir) (LB dir) (UB_upd dir) ((update\<B> (UB_upd dir) x c s))"
  assumes "\<And> c x dir. 
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)); 
       \<not> ((lt dir) c (\<langle>\<V> s\<rangle> x))
     \<rbrakk> \<Longrightarrow> 
        P' (lt dir) (UB dir) (LB dir) (UB_upd dir) ((update\<B> (UB_upd dir) x c s))"

  assumes "\<And> s. P s = P' (op >) \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>l_update s"
  assumes "\<And> s. P s = P' (op <) \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>u_update s"
  shows "P (assert_bound a s)"
proof (cases a)
  case (Leq x c)
  thus ?thesis
    apply (simp del: assert_bound'_def)
    apply (rule assert_bound'_cases, simp_all)
    using assms(1)[of Positive x c]
    using assms(2)[of Positive x c]
    using assms(3)[of Positive x c]
    using assms(4)[of Positive x c]
    using assms(5)[of Positive x c]
    using assms(7)
    by auto
next
  case (Geq x c)
  thus ?thesis
    apply (simp del: assert_bound'_def)
    apply (rule assert_bound'_cases)
    using assms(1)[of Negative x c]
    using assms(2)[of Negative x c]
    using assms(3)[of Negative x c]
    using assms(4)[of Negative x c]
    using assms(5)[of Negative x c]
    using assms(6)
    by auto
qed
(*>*)
(*<*)
end
(*>*)
(*<*)
lemma decrease_ub_satisfied_inverse:
  assumes "\<lhd>\<^sub>u\<^sub>b (lt dir) c  (UB dir s x)" "dir = Positive \<or> dir = Negative"
  assumes "v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)"
  shows "v \<Turnstile>\<^sub>b \<B> s"
  unfolding satisfies_bounds.simps
proof
  fix x'
  show "in_bounds x' v (\<B> s)"
  proof (cases "x = x'")
    case False
    thus ?thesis
      using `v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)` `dir = Positive \<or> dir = Negative`
      unfolding satisfies_bounds.simps
      by (auto split: if_splits)
  next
    case True
    thus ?thesis
      using `v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)` `dir = Positive \<or> dir = Negative`
      unfolding satisfies_bounds.simps
      using `\<lhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)`
      by (erule_tac x="x'" in allE)
         (auto simp add: lt_ubound_def[THEN sym] gt_lbound_def[THEN sym] compare_strict_nonstrict)
  qed
qed

lemma atoms_equiv_bounds_extend:
  fixes x c dir
  assumes "dir = Positive \<or> dir = Negative"  "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)"  "ats \<doteq> \<B> s" 
  shows "(ats \<union> {LE dir x c}) \<doteq> \<B> (update\<B> (UB_upd dir) x c s)"
  unfolding atoms_equiv_bounds.simps
proof
  fix v
  show "v \<Turnstile>\<^sub>a\<^sub>s (ats \<union> {LE dir x c}) = v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)"
  proof
    assume "v \<Turnstile>\<^sub>a\<^sub>s (ats \<union> {LE dir x c})"
    hence "v \<Turnstile>\<^sub>a\<^sub>s ats" "le (lt dir) (v x) c"
      using `dir = Positive \<or> dir = Negative`
      unfolding satisfies_atom_set_def
      by auto
    show "v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)"
      unfolding satisfies_bounds.simps
    proof
      fix x'
      show "in_bounds x' v (\<B> (update\<B> (UB_upd dir) x c s))"
        using `v \<Turnstile>\<^sub>a\<^sub>s ats` `le (lt dir) (v x) c` `ats \<doteq> \<B> s`
        using `dir = Positive \<or> dir = Negative`
        unfolding atoms_equiv_bounds.simps satisfies_bounds.simps
        by (cases "x = x'") auto
    qed
  next
    assume "v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)"
    hence "v \<Turnstile>\<^sub>b \<B> s"
      using `\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)`
      using `dir = Positive \<or> dir = Negative`
      using decrease_ub_satisfied_inverse[of dir c s x v]
      using neg_bounds_compare(1)[of c "\<B>\<^sub>u s x"]
      using neg_bounds_compare(5)[of c "\<B>\<^sub>l s x"]
      by (auto simp add:  lt_ubound_def[THEN sym] ge_ubound_def[THEN sym] le_lbound_def[THEN sym] gt_lbound_def[THEN sym])
    show "v \<Turnstile>\<^sub>a\<^sub>s (ats \<union> {LE dir x c})"
      unfolding satisfies_atom_set_def
    proof
      fix a
      assume "a \<in> ats \<union> {LE dir x c}"
      thus "v \<Turnstile>\<^sub>a a"
      proof
        assume "a \<in> {LE dir x c}"
        thus ?thesis
          using `v \<Turnstile>\<^sub>b \<B> (update\<B> (UB_upd dir) x c s)`
          using `dir = Positive \<or> dir = Negative`
          unfolding satisfies_bounds.simps
          by (auto split: if_splits)
      next
        assume "a \<in> ats"
        thus ?thesis
          using `ats \<doteq> \<B> s`
          using `v \<Turnstile>\<^sub>b \<B> s`
          unfolding atoms_equiv_bounds.simps satisfies_atom_set_def
          by auto
      qed
    qed
  qed
qed
(*>*)
text{* Given the @{term update} function, @{text assert_bound} can be
implemented as follows.
\vspace{-2mm}
@{text[display]
  "assert_bound (Leq x c) s \<equiv>
          if c \<ge>\<^sub>u\<^sub>b \<B>\<^sub>u s x then s
          else let s' = s \<lparr> \<B>\<^sub>u := (\<B>\<^sub>u s) (x := Some c) \<rparr>
               in if c <\<^sub>l\<^sub>b \<B>\<^sub>l s x then s' \<lparr> \<U> := True \<rparr>
               else if x \<notin> lvars (\<T> s') \<and> c < \<langle>\<V> s\<rangle> x then update x c s' else s'"
}
\vspace{-2mm}
\noindent The case of @{text "Geq x c"} atoms is analogous (a systematic way to
avoid symmetries is discussed in Section \ref{sec:symmetries}). This
implementation satisfies both its specifications.
*}
(*<*)
sublocale Update < AssertBoundNoLhs assert_bound
proof
  fix s::"'a state" and a
  assume "\<not> \<U> s" "\<triangle> (\<T> s)" "\<nabla> s"
  thus "\<T> (assert_bound a s) = \<T> s"
    by (cases a) (auto simp add: Let_def update_tableau_id tableau_valuated_def)
next
  fix s::"'a state" and a
  assume *: "\<not> \<U> s" "\<triangle> (\<T> s)" "\<nabla> s"
  show "\<U> (assert_bound a s) \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s assert_bound a s)" (is "?P (assert_bound a s)")
  proof-
    let ?P' = "\<lambda> lt UB LB UB_upd s. \<U> s \<longrightarrow> \<not> (\<exists>v. (\<forall>x. ((\<unrhd>\<^sub>l\<^sub>b lt (v x) (LB s x)) \<and> \<unlhd>\<^sub>u\<^sub>b lt (v x) (UB s x))) \<and> v \<Turnstile>\<^sub>t \<T> s)"
    show ?thesis
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix s'
      show "?P s' = ?P' op < \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>u_upd s'" "?P s' = ?P' (op >) \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>l_upd s'"
        unfolding satisfies_state_def satisfies_bounds.simps in_bounds.simps
        unfolding bound_compare''_defs
        by auto
    next
      fix c::'a and x::nat and dir
      assume "\<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)" "dir = Positive \<or> dir = Negative"
      thus "?P' (lt dir) (UB dir) (LB dir) (UB_upd dir) (update\<B> (UB_upd dir) x c s \<lparr>\<U> := True\<rparr>)"
        by (cases "LB dir s x", auto simp add: bound_compare'_defs)
           (erule_tac x=x in allE, auto)+
    next
      fix c::'a and x::nat and dir
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "x \<notin> lvars (\<T> s)" "lt dir c (\<langle>\<V> s\<rangle> x)" "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
      thus "\<U> (update x c (update\<B> (UB_upd dir) x c s)) \<longrightarrow>
          \<not> (\<exists>v. (\<forall>xa. \<unrhd>\<^sub>l\<^sub>b (lt dir) (v xa) (LB dir (update x c (update\<B> (UB_upd dir) x c s)) xa) \<and>
                       \<unlhd>\<^sub>u\<^sub>b (lt dir) (v xa) (UB dir (update x c (update\<B> (UB_upd dir) x c s)) xa)) \<and>
                 v \<Turnstile>\<^sub>t \<T> (update x c (update\<B> (UB_upd dir) x c s)))"
        using *
        by (auto simp add: update_unsat_id tableau_valuated_def)
    qed (auto simp add: * update_unsat_id tableau_valuated_def)
  qed
next
  fix s::"'a state" and a
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"

  show "\<not> \<U> (assert_bound a s) \<longrightarrow>  \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound a s) \<and> \<diamond> (assert_bound a s)" (is "?lhs \<longrightarrow> ?rhs")
  proof
    assume ?lhs
    have "\<langle>\<V> (assert_bound a s)\<rangle> \<Turnstile>\<^sub>t \<T> (assert_bound a s)"
    proof-
      let ?P = "\<lambda> lt UB LB UB_upd s. \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
      show ?thesis
      proof (rule assert_bound_cases[of _ _ ?P])
        fix c x and dir :: "'a Direction"
        let ?s' = "update\<B> (UB_upd dir) x c s"
        assume "x \<notin> lvars (\<T> s)" "(lt dir) c (\<langle>\<V> s\<rangle> x)"
               "dir = Positive \<or> dir = Negative"
        thus "\<langle>\<V> (update x c ?s')\<rangle> \<Turnstile>\<^sub>t \<T> (update x c ?s')"
          using *
          using update_satisfies_tableau[of ?s' x c] update_tableau_id
          by (auto simp add: curr_val_satisfies_no_lhs_def tableau_valuated_def)
      qed (insert *, auto simp add: curr_val_satisfies_no_lhs_def)
    qed
    moreover
    have "\<not> \<U> (assert_bound a s) \<longrightarrow> \<langle>\<V> (assert_bound a s)\<rangle> \<Turnstile>\<^sub>b \<B> (assert_bound a s) \<parallel> - lvars (\<T> (assert_bound a s))" (is "?P (assert_bound a s)")
    proof-
      let ?P' = "\<lambda> lt UB LB UB_upd s. 
        \<not> \<U> s \<longrightarrow> (\<forall>x\<in>- lvars (\<T> s). \<unrhd>\<^sub>l\<^sub>b lt (\<langle>\<V> s\<rangle> x) (LB s x) \<and> \<unlhd>\<^sub>u\<^sub>b lt (\<langle>\<V> s\<rangle> x) (UB s x))"
      let ?P'' = "\<lambda> dir. ?P' (lt dir) (UB dir) (LB dir) (UB_upd dir)"

      have x: "\<And> s'. ?P s' = ?P' (op <) \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>u_update s'"
       and xx: "\<And> s'. ?P s' = ?P' (op >) \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>l_update s'"
        unfolding satisfies_bounds_set.simps in_bounds.simps bound_compare_defs
        by (auto split: option.split)

      show ?thesis
      proof (rule assert_bound_cases[of _ _ ?P'])
        fix dir :: "'a Direction"
        assume "dir = Positive \<or> dir = Negative"
        thus "?P'' dir s"
          using  x[of s] xx[of s] `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`
          by (auto simp add: curr_val_satisfies_no_lhs_def)
      next
        fix x c and dir :: "'a Direction"
        let ?s' = "update\<B> (UB_upd dir) x c s"
        assume "x \<in> lvars (\<T> s)" "dir = Positive \<or> dir = Negative"
        hence "?P ?s'"
          using `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`
          by (auto simp add: satisfies_bounds_set.simps curr_val_satisfies_no_lhs_def)
        thus "?P'' dir ?s'"
          using x[of ?s'] xx[of ?s'] `dir = Positive \<or> dir = Negative`
          by auto
      next
        fix c x and dir :: "'a Direction"
        let ?s' = "update\<B> (UB_upd dir) x c s"
        assume "\<not> lt dir c (\<langle>\<V> s\<rangle> x)" "dir = Positive \<or> dir = Negative"
        thus "?P'' dir ?s'"
          using `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`
          by (auto simp add: satisfies_bounds_set.simps curr_val_satisfies_no_lhs_def) (auto simp add: bound_compare_defs)
      next
        fix c x and dir :: "'a Direction"
        let ?s' = "update x c (update\<B> (UB_upd dir) x c s)"
        assume "x \<notin> lvars (\<T> s)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
          "dir = Positive \<or> dir = Negative"
        show "?P'' dir ?s'"
        proof (rule impI, rule ballI)
          fix x'
          assume "\<not> \<U> ?s'" "x' \<in> - lvars (\<T> ?s')"
          show "\<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> ?s'\<rangle> x') (LB dir ?s' x') \<and> \<unlhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> ?s'\<rangle> x') (UB dir ?s' x')"
          proof (cases "x = x'")
            case True
            thus ?thesis
              using `x \<notin> lvars (\<T> s)`
              using `x' \<in> - lvars (\<T> ?s')`
              using `\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)`
              using `dir = Positive \<or> dir = Negative`
              using neg_bounds_compare(7) neg_bounds_compare(3)
              using *
              by (auto simp add: update_valuation_nonlhs update_tableau_id update_bounds_id bound_compare''_defs map2fun_def tableau_valuated_def) (force simp add: bound_compare'_defs)+
          next
            case False
            thus ?thesis
              using `x \<notin> lvars (\<T> s)` `x' \<in> - lvars (\<T> ?s')`
              using `dir = Positive \<or> dir = Negative` *
              by (auto simp add: update_valuation_nonlhs update_tableau_id update_bounds_id  bound_compare''_defs satisfies_bounds_set.simps curr_val_satisfies_no_lhs_def map2fun_def tableau_valuated_def)
          qed
        qed
      qed (auto simp add: x xx)
    qed
    moreover
    have "\<not> \<U> (assert_bound a s) \<longrightarrow> \<diamond> (assert_bound a s)" (is "?P (assert_bound a s)")
    proof-
      let ?P' = "\<lambda> lt UB LB UB_upd s. 
        \<not> \<U> s \<longrightarrow>
        (\<forall>x. if LB s x = None \<or> UB s x = None then True
             else lt (the (LB s x)) (the (UB s x)) \<or> (the (LB s x) = the (UB s x)))"
      let ?P'' = "\<lambda> dir. ?P' (lt dir) (UB dir) (LB dir) (UB_upd dir)"

      have x: "\<And> s'. ?P s' = ?P' (op <) \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>u_update s'" and
           xx: "\<And> s'. ?P s' = ?P' (op >) \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>l_update s'"
        unfolding bounds_consistent_def
        by auto

      show ?thesis
      proof (rule assert_bound_cases[of _ _ ?P'])
        fix dir :: "'a Direction"
        assume "dir = Positive \<or> dir = Negative"
        thus "?P'' dir s"
          using `\<diamond> s`
          by (auto simp add: bounds_consistent_def) (erule_tac x=x in allE, auto)+
      next
        fix x c and dir :: "'a Direction"
        let ?s' = "update x c (update\<B> (UB_upd dir) x c s)"
        assume "dir = Positive \<or> dir = Negative" "x \<notin> lvars (\<T> s)"
          "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
        thus "?P'' dir ?s'"
          using `\<diamond> s` *
          unfolding bounds_consistent_def
          by (auto simp add: update_bounds_id tableau_valuated_def split: if_splits)
             (force simp add: bound_compare'_defs, erule_tac x=xa in allE, simp)+
      next
        fix x c and dir :: "'a Direction"
        let ?s' = "update\<B> (UB_upd dir) x c s"
        assume "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
          "dir = Positive \<or> dir = Negative"
        hence "?P'' dir ?s'"
          using `\<diamond> s`
          unfolding bounds_consistent_def
          by (auto split: if_splits) (force simp add: bound_compare'_defs, erule_tac x=xa in allE, simp)+
        thus "?P'' dir ?s'" "?P'' dir ?s'"
          by simp_all
      qed (auto simp add: x xx)
    qed

    ultimately

    show ?rhs
      using `?lhs`
      unfolding curr_val_satisfies_no_lhs_def
      by simp
  qed
next
  fix s :: "'a state" and ats a
  assume "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s"
  show "ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> (assert_bound a s)" (is "?P (assert_bound a s)")
  proof-
    let ?P' = "\<lambda> lt UB LB UB_upd s'. ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> s'"
    let ?P'' = "\<lambda> dir. ?P' (lt dir) (UB dir) (LB dir) (UB_upd dir)"
    show ?thesis
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix x c and dir :: "'a Direction"
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)"
      thus "?P s"
        unfolding atoms_equiv_bounds.simps satisfies_atom_set_def satisfies_bounds.simps
        by auto (erule_tac x=x in allE, force simp add: bound_compare_defs)+
    next
      fix x c and dir :: "'a Direction"
      let ?s' = "update\<B> (UB_upd dir) x c s\<lparr>\<U> := True\<rparr>"
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x))"
      thus "?P ?s'"
        using atoms_equiv_bounds_extend[of dir c s x ats]
        by auto
    next
      fix x c and dir :: "'a Direction"
      let ?s' = "update\<B> (UB_upd dir) x c s"
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x))"
      hence "?P ?s'"
        using atoms_equiv_bounds_extend[of dir c s x ats]
        by auto
      thus "?P ?s'" "?P ?s'"
        by simp_all
    next
      fix x c and dir :: "'a Direction"
      let ?s' = "update x c (update\<B> (UB_upd dir) x c s)"
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x))" "x \<notin> lvars (\<T> s)"
      thus "?P ?s'"
        using atoms_equiv_bounds_extend[of dir c s x ats]
        using `\<triangle> (\<T> s)` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s` `\<nabla> s`
        by (auto simp add: fun_upd_def update_bounds_id tableau_valuated_def)
    qed simp_all
  qed
next
  fix s a
  fix s :: "'a state" and ats a
  assume "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s"
  have *: "\<And> dir x c s. dir = Positive \<or> dir = Negative \<Longrightarrow> (\<nabla> (update\<B> (UB_upd dir) x c s) = \<nabla> s)" "\<And> s. \<nabla> (s\<lparr>\<U> := True\<rparr>) = \<nabla> s"
    by (auto simp add: tableau_valuated_def)

  show "\<nabla> (assert_bound a s)" (is "?P (assert_bound a s)")
  proof-
    let ?P' = "\<lambda> lt UB LB UB_upd s'. \<nabla> s'"
    let ?P'' = "\<lambda> dir. ?P' (lt dir) (UB dir) (LB dir) (UB_upd dir)"
    show ?thesis
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix x c and dir :: "'a Direction"
      assume "dir = Positive \<or> dir = Negative"
      hence "\<nabla> (update\<B> (UB_upd dir) x c s)"
        using *(1)[of dir x c s] `\<nabla> s`
        by simp
      thus "\<nabla> (update\<B> (UB_upd dir) x c s\<lparr>\<U> := True\<rparr>)"
        using *(2)
        by auto
    next
      fix x c and dir :: "'a Direction"
      assume "x \<notin> lvars (\<T> s)" "dir = Positive \<or> dir = Negative"
      thus "\<nabla> (update x c (update\<B> (UB_upd dir) x c s))"
        using `\<triangle> (\<T> s)` `\<nabla> s`
        using update_tableau_valuated[of "(update\<B> (UB_upd dir) x c s)" x c]
        by (auto simp add: tableau_valuated_def)
    qed (insert `\<nabla> s` *(1), auto)
  qed
qed
(*>*)
(*<*)

locale EqForLVar = 
  fixes eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat"
  assumes eq_idx_for_lvar:
    "\<lbrakk>x \<in> lvars t\<rbrakk> \<Longrightarrow> eq_idx_for_lvar t x < length t \<and> lhs (t ! eq_idx_for_lvar t x) = x"
begin
definition eq_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> eq" where
  "eq_for_lvar t v \<equiv> t ! (eq_idx_for_lvar t v)"
lemma eq_for_lvar: 
  "\<lbrakk>x \<in> lvars t\<rbrakk> \<Longrightarrow> eq_for_lvar t x \<in> set t \<and> lhs (eq_for_lvar t x) = x"
unfolding eq_for_lvar_def
using eq_idx_for_lvar
by auto

abbreviation rvars_of_lvar where 
 "rvars_of_lvar t x \<equiv> rvars_eq (eq_for_lvar t x)"

lemma rvars_of_lvar_rvars:
  assumes "x \<in> lvars t"
  shows "rvars_of_lvar t x \<subseteq> rvars t"
using assms eq_for_lvar[of x t]
unfolding rvars_def
by auto

end
(*>*)
text {* Updating changes the value of @{text x} and then updates
values of all lhs variables so that the tableau remains
satisfied. This can be based on a function that recalculates rhs
polynomial values in the changed valuation: *}

locale RhsEqVal = fixes rhs_eq_val::"(var, 'a::lrv) mapping \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> eq \<Rightarrow> 'a"
  --{* --- @{text rhs_eq_val} computes the value of the rhs of @{text e} in @{text "\<langle>v\<rangle>(x := c)"}. *}
  assumes (*<*)rhs_eq_val: (*>*) "\<langle>v\<rangle> \<Turnstile>\<^sub>e e \<Longrightarrow> rhs_eq_val v x c e = rhs e \<lbrace> \<langle>v\<rangle> (x := c) \<rbrace>"
(*<*)
begin
(*>*)
text{* \noindent Then, the next implementation of @{text update}
satisfies its specification: *}

(*<*)abbreviation update_eq where(*>*)
"update_eq v x c v' e \<equiv> upd (lhs e) (rhs_eq_val v x c e) v'"

(*<*)definition update :: "var \<Rightarrow> 'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where(*>*)
"update x c s \<equiv> s\<lparr>\<V> := upd x c (foldl (update_eq (\<V> s) x c) (\<V> s) (\<T> s))\<rparr>"
(*<*)
lemma update_no_set_none:
  shows "look (\<V> s) y \<noteq> None \<Longrightarrow> 
         look (foldl (update_eq (\<V> s) x v) (\<V> s) t) y \<noteq> None"
  by (induct t rule: rev_induct, auto simp: lookup_update')

lemma update_no_left:
  assumes  "y \<notin> lvars t"
  shows "look (\<V> s) y = look (foldl (update_eq (\<V> s) x v) (\<V> s) t) y"
using assms
by (induct t rule: rev_induct) (auto simp add: lvars_def lookup_update')

lemma update_left: 
  assumes "y \<in> lvars t"
  shows "\<exists> eq \<in> set t. lhs eq = y \<and> 
     look (foldl (update_eq (\<V> s) x v) (\<V> s) t) y = Some (rhs_eq_val (\<V> s) x v eq)"
using assms
by (induct t rule: rev_induct) (auto simp add: lvars_def lookup_update')

lemma update_valuate_rhs:
  assumes "e \<in> set (\<T> s)" "\<triangle> (\<T> s)"
  shows "rhs e \<lbrace> \<langle>\<V> (update x c s)\<rangle> \<rbrace> = rhs e \<lbrace> \<langle>\<V> s\<rangle> (x := c) \<rbrace>"
proof (rule valuate_depend, safe)
  fix y
  assume "y \<in> rvars_eq e"
  hence "y \<notin> lvars (\<T> s)"
    using `\<triangle> (\<T> s)` `e \<in> set (\<T> s)`
    by (auto simp add: normalized_tableau_def rvars_def)
  thus "\<langle>\<V> (update x c s)\<rangle> y = (\<langle>\<V> s\<rangle>(x := c)) y"
    using update_no_left[of y "\<T> s" s x c]
    by (auto simp add: update_def map2fun_def lookup_update')
qed

end
(*>*)
(*<*)
sublocale RhsEqVal < Update update
proof
  fix s::"'a state" and x c
  show "let s' = update x c s in \<T> s' = \<T> s \<and> \<B> s' = \<B> s \<and> \<U> s' = \<U> s"
    by (simp add: Let_def update_def)
next
  fix s::"'a state" and x c
  assume "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  thus "\<nabla> (update x c s)"
    using update_no_set_none[of s]
    by (simp add: Let_def update_def tableau_valuated_def lookup_update')
next
  fix s::"'a state" and  x x' c
  assume "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  show "x' \<notin> lvars (\<T> s) \<longrightarrow>
          look (\<V> (update x c s)) x' =
          (if x = x' then Some c else look (\<V> s) x')"
    using update_no_left[of x' "\<T> s" s x c]
    unfolding update_def lvars_def Let_def
    by (auto simp: lookup_update')
next
  fix s::"'a state" and x c
  assume "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  have "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<Longrightarrow> \<forall>e \<in> set (\<T> s). \<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>e e"
  proof
    fix e
    assume "e \<in> set (\<T> s)" "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
    hence "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>e e"
      by (simp add: satisfies_tableau_def)

    have "x \<noteq> lhs e"
      using `x \<notin> lvars (\<T> s)` `e \<in> set (\<T> s)`
      by (auto simp add: lvars_def)
    hence "\<langle>\<V> (update x c s)\<rangle> (lhs e) = rhs_eq_val (\<V> s) x c e"
      using update_left[of "lhs e" "\<T> s" s x c] `e \<in> set (\<T> s)` `\<triangle> (\<T> s)`
      by (auto simp add: lvars_def lookup_update' update_def Let_def map2fun_def normalized_tableau_def distinct_map inj_on_def)
    thus "\<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>e e"
      using `\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>e e` `e \<in> set (\<T> s)` `x \<notin> lvars (\<T> s)` `\<triangle> (\<T> s)`
      using update_valuate_rhs rhs_eq_val
      by (simp add: satisfies_eq_def)
  qed
  thus "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<longrightarrow> \<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>t \<T> s"
    by(simp add: satisfies_tableau_def update_def)
qed
(*>*)

text{* To update the valuation for a variable that is on the lhs of
the tableau it should first be swapped with some rhs variable of its
equation, in an operation called \emph{pivoting}. Pivoting has the
precondition that the tableau is normalized and that it is always
called for a lhs variable of the tableau, and a rhs variable in the
equation with that lhs variable. The set of rhs variables for the
given lhs variable is found using the @{text rvars_of_lvar} function
(specified in a very simple locale @{text EqForLVar}, that we do not
print). *}

locale Pivot = EqForLVar + fixes pivot::"var \<Rightarrow> var \<Rightarrow> 'a::lrv state \<Rightarrow> 'a state"
assumes
  -- {* --- Valuation, bounds, and the unsatisfiability flag are not changed. *}

(*<*)pivot_id: (*>*) "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      let s' = pivot x\<^sub>i x\<^sub>j s in \<V> s' = \<V> s \<and> \<B> s' = \<B> s \<and> \<U> s' = \<U> s" (*<*)and(*>*)

  -- {* --- The tableau remains equivalent to the previous one and normalized. *}

(*<*) pivot_tableau: (*>*) "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      let s' = pivot x\<^sub>i x\<^sub>j s in  ((v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') " (*<*)and(*>*)

-- {* --- @{text "x\<^sub>i"} and @{text "x\<^sub>j"} are swapped, while the other variables do not change sides. *}

(*<*) pivot_vars':  (*>*) "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> let s' = pivot x\<^sub>i x\<^sub>j s in
   rvars(\<T> s') = rvars(\<T> s)-{x\<^sub>j}\<union>{x\<^sub>i}  \<and>  lvars(\<T> s') = lvars(\<T> s)-{x\<^sub>i}\<union>{x\<^sub>j}"
(*<*)
begin
lemma pivot_bounds_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      \<B>\<^sub>l (pivot x\<^sub>i x\<^sub>j s) = \<B>\<^sub>l s \<and> \<B>\<^sub>u (pivot x\<^sub>i x\<^sub>j s) = \<B>\<^sub>u s"
using pivot_id
by (simp add: Let_def)

lemma pivot_valuation_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<V> (pivot x\<^sub>i x\<^sub>j s) = \<V> s"
using pivot_id
by (simp add: Let_def)

lemma pivot_unsat_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<U> (pivot x\<^sub>i x\<^sub>j s) = \<U> s"
using pivot_id
by (simp add: Let_def)

lemma pivot_tableau_equiv: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      (v::'a valuation) \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> (pivot x\<^sub>i x\<^sub>j s)"
using pivot_tableau
by (simp add: Let_def)

lemma pivot_tableau_normalized: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<triangle> (\<T> (pivot x\<^sub>i x\<^sub>j s))"
using pivot_tableau
by (simp add: Let_def)

lemma pivot_rvars: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> rvars (\<T> (pivot x\<^sub>i x\<^sub>j s)) = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
using pivot_vars'
by (simp add: Let_def)

lemma pivot_lvars: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> lvars (\<T> (pivot x\<^sub>i x\<^sub>j s)) = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
using pivot_vars'
by (simp add: Let_def)

lemma pivot_vars:
  "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> tvars (\<T> (pivot x\<^sub>i x\<^sub>j s)) = tvars (\<T> s) "
  using pivot_lvars[of s x\<^sub>i x\<^sub>j] pivot_rvars[of s x\<^sub>i x\<^sub>j]
  using rvars_of_lvar_rvars[of x\<^sub>i "\<T> s"]
  by auto

lemma 
  pivot_tableau_valuated: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i; \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (pivot x\<^sub>i x\<^sub>j s)"
  using pivot_valuation_id pivot_vars
  by (auto simp add: tableau_valuated_def)

end
(*>*)

text{* Functions @{text pivot} and @{text update} can be used to
implement the @{text check} function. In its context, @{text pivot}
and @{text update} functions are always called together, so the
following definition can be used: @{prop "pivot_and_update x\<^sub>i x\<^sub>j c s =
update x\<^sub>i c (pivot x\<^sub>i x\<^sub>j s)"}. It is possible to make a more efficient
implementation of @{text pivot_and_update} that does not use separate
implementations of @{text pivot} and @{text update}. To allow this, a
separate specification for @{text pivot_and_update} can be given. It can be
easily shown that the @{text pivot_and_update} definition above
satisfies this specification. *}

(*<*)
locale PivotAndUpdate = EqForLVar + 
  fixes pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a::lrv \<Rightarrow> 'a state \<Rightarrow> 'a state"
assumes (*<*) pivotandupdate_unsat_id:  (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      \<U> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<U> s"
assumes (*<*) pivotandupdate_bounds_id: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      \<B> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<B> s"
assumes (*<*) pivotandupdate_tableau_normalized: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      \<triangle> (\<T> (pivot_and_update x\<^sub>i x\<^sub>j c s))"
assumes (*<*) pivotandupdate_tableau_equiv: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      (v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (pivot_and_update x\<^sub>i x\<^sub>j c s)"
  assumes (*<*)pivotandupdate_satisfies_tableau: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<longrightarrow> \<langle>\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)\<rangle> \<Turnstile>\<^sub>t \<T> s"
assumes (*<*) pivotandupdate_rvars:  (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      rvars (\<T> (pivot_and_update x\<^sub>i x\<^sub>j c s)) = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
assumes (*<*) pivotandupdate_lvars: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      lvars (\<T> (pivot_and_update x\<^sub>i x\<^sub>j c s)) = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  assumes (*<*)pivotandupdate_valuation_nonlhs: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
      x \<notin> lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j} \<longrightarrow> look (\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)) x = (if x = x\<^sub>i then Some c else look (\<V> s) x)"
  assumes (*<*)pivotandupdate_tableau_valuated: (*>*) "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> 
 \<nabla> (pivot_and_update x\<^sub>i x\<^sub>j c s)"
begin
lemma  pivotandupdate_valuation_xi: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> look (\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)) x\<^sub>i = Some c"
using pivotandupdate_valuation_nonlhs[of s x\<^sub>i x\<^sub>j x\<^sub>i c]
using rvars_of_lvar_rvars
by (auto simp add:  normalized_tableau_def)

lemma  pivotandupdate_valuation_other_nolhs: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i; x \<notin> lvars (\<T> s); x \<noteq> x\<^sub>j\<rbrakk> \<Longrightarrow> look (\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)) x = look (\<V> s) x"
using pivotandupdate_valuation_nonlhs[of s x\<^sub>i x\<^sub>j x c]
by auto

lemma pivotandupdate_nolhs: 
  "\<lbrakk> \<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i;
     \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<B>\<^sub>l s x\<^sub>i = Some c \<or> \<B>\<^sub>u s x\<^sub>i = Some c\<rbrakk> \<Longrightarrow> 
     \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (pivot_and_update x\<^sub>i x\<^sub>j c s)"
  using pivotandupdate_satisfies_tableau[of s x\<^sub>i x\<^sub>j c]
  using pivotandupdate_tableau_equiv[of s x\<^sub>i x\<^sub>j _ c]
  using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c]
  using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j _ c]
  using pivotandupdate_lvars[of s x\<^sub>i x\<^sub>j c]
  by (auto simp add: curr_val_satisfies_no_lhs_def satisfies_bounds.simps satisfies_bounds_set.simps pivotandupdate_bounds_id bounds_consistent_geq_lb bounds_consistent_leq_ub map2fun_def)

lemma pivotandupdate_bounds_consistent:
  assumes "\<triangle> (\<T> s)" "\<nabla> s" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
  shows "\<diamond> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<diamond> s"
  using assms pivotandupdate_bounds_id[of s x\<^sub>i x\<^sub>j c]
  by (simp add: bounds_consistent_def)
end
(*>*)
(*<*)
locale PivotUpdate = Pivot eq_idx_for_lvar pivot + Update update for
 eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat" and
 pivot :: "var \<Rightarrow> var \<Rightarrow> 'a::lrv state \<Rightarrow> 'a state" and
 update :: "var \<Rightarrow> 'a \<Rightarrow> 'a state \<Rightarrow> 'a state"
begin
definition  pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where [simp]:
 "pivot_and_update x\<^sub>i x\<^sub>j c s \<equiv> update x\<^sub>i c (pivot x\<^sub>i x\<^sub>j s)"

lemma pivot_update_precond: 
  assumes "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
  shows "\<triangle> (\<T> (pivot x\<^sub>i x\<^sub>j s))" "x\<^sub>i \<notin> lvars (\<T> (pivot x\<^sub>i x\<^sub>j s))"
proof-
  from assms have "x\<^sub>i \<noteq> x\<^sub>j"
    using rvars_of_lvar_rvars[of x\<^sub>i "\<T> s"]
    by (auto simp add: normalized_tableau_def)
  thus "\<triangle> (\<T> (pivot x\<^sub>i x\<^sub>j s))" "x\<^sub>i \<notin> lvars (\<T> (pivot x\<^sub>i x\<^sub>j s))"
    using assms 
    using pivot_tableau_normalized[of s x\<^sub>i x\<^sub>j]
    using pivot_lvars[of s x\<^sub>i x\<^sub>j]
    by auto
qed

end
(*>*)
(*<*)
sublocale PivotUpdate < PivotAndUpdate eq_idx_for_lvar pivot_and_update
  using pivot_update_precond
  using update_unsat_id pivot_unsat_id update_bounds_id pivot_bounds_id update_tableau_id pivot_tableau_normalized pivot_tableau_equiv update_satisfies_tableau pivot_valuation_id pivot_lvars pivot_rvars  update_valuation_nonlhs update_valuation_nonlhs pivot_tableau_valuated update_tableau_valuated
  by (unfold_locales) auto
(*>*)

text {* Pivoting the tableau can be reduced to pivoting single equations,
  and substituting variable by polynomials. These operations are specified 
  by: *}

locale PivotEq = fixes pivot_eq::"eq \<Rightarrow> var \<Rightarrow> eq"
assumes
-- {* --- Lhs var of @{text eq} and @{text x\<^sub>j} are swapped,
     while the other variables do not change sides. *}
(*<*)vars_pivot_eq:(*>*)"
\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow> let eq' = pivot_eq eq x\<^sub>j in
    lhs eq' = x\<^sub>j \<and> rvars_eq eq' = {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})" (*<*)and(*>*)

-- {* --- Pivoting keeps the equation equisatisfiable. *}

(*<*)equiv_pivot_eq:(*>*)
"\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow>
    (v::'a::lrv valuation) \<Turnstile>\<^sub>e pivot_eq eq x\<^sub>j \<longleftrightarrow> v \<Turnstile>\<^sub>e eq"
(*<*)
begin

lemma lhs_pivot_eq:
  "\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow> lhs (pivot_eq eq x\<^sub>j) = x\<^sub>j"
  using vars_pivot_eq
  by (simp add: Let_def)

lemma rvars_pivot_eq:
  "\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow> rvars_eq (pivot_eq eq x\<^sub>j) = {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
  using vars_pivot_eq
  by (simp add: Let_def)

end
(*>*)
(*<*)
abbreviation doublesub (" _ \<subseteq>s _ \<subseteq>s _" [50,51,51] 50) where
 "doublesub a b c \<equiv> a \<subseteq> b \<and> b \<subseteq> c"
(*>*)

locale SubstVar = fixes subst_var::"var \<Rightarrow> linear_poly \<Rightarrow> linear_poly \<Rightarrow> linear_poly"
assumes
-- {* --- Effect of @{text "subst_var x\<^sub>j lp' lp"} on @{text lp} variables. *}

(*<*)vars_subst_var':(*>*)
"(vars lp - {x\<^sub>j}) - vars lp' \<subseteq>s vars (subst_var x\<^sub>j lp' lp) \<subseteq>s (vars lp - {x\<^sub>j}) \<union> vars lp'"(*<*)and(*>*)

-- {* --- Effect of @{text "subst_var x\<^sub>j lp' lp"} on @{text lp} value. *}

(*<*)equiv_subst_var:(*>*)
"(v::'a::lrv valuation) x\<^sub>j = lp' \<lbrace>v\<rbrace> \<longrightarrow> lp \<lbrace>v\<rbrace> = (subst_var x\<^sub>j lp' lp) \<lbrace>v\<rbrace>"
(*<*)
begin

lemma vars_subst_var:
"vars (subst_var x\<^sub>j lp' lp) \<subseteq> (vars lp - {x\<^sub>j}) \<union> vars lp'"
using vars_subst_var'
by simp

lemma vars_subst_var_supset:
"vars (subst_var x\<^sub>j lp' lp) \<supseteq> (vars lp - {x\<^sub>j}) - vars lp'"
using vars_subst_var'
by simp

definition subst_var_eq :: "var \<Rightarrow> linear_poly \<Rightarrow> eq \<Rightarrow> eq" where
  "subst_var_eq v lp' eq \<equiv> (lhs eq, subst_var v lp' (rhs eq))"

lemma rvars_eq_subst_var_eq:
  shows "rvars_eq (subst_var_eq x\<^sub>j lp eq) \<subseteq> (rvars_eq eq - {x\<^sub>j}) \<union> vars lp"
  unfolding subst_var_eq_def
  by (auto simp add: vars_subst_var)

lemma rvars_eq_subst_var_eq_supset:
  "rvars_eq (subst_var_eq x\<^sub>j lp eq) \<supseteq> (rvars_eq eq) - {x\<^sub>j} - (vars lp)"
  unfolding subst_var_eq_def
  by (simp add: vars_subst_var_supset)

lemma equiv_subst_var_eq:
  assumes "(v::'a valuation) \<Turnstile>\<^sub>e (x\<^sub>j, lp')"
  shows "v \<Turnstile>\<^sub>e eq \<longleftrightarrow> v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j lp' eq"
  using assms
  unfolding subst_var_eq_def
  unfolding satisfies_eq_def
  using equiv_subst_var[of v x\<^sub>j lp' "rhs eq"]
  by auto
end

locale Pivot' = EqForLVar + PivotEq + SubstVar
begin
definition pivot_tableau' :: "var \<Rightarrow> var \<Rightarrow> tableau \<Rightarrow> tableau" where
"pivot_tableau' x\<^sub>i x\<^sub>j t \<equiv>
    let x\<^sub>i_idx = eq_idx_for_lvar t x\<^sub>i; eq = t ! x\<^sub>i_idx; eq' = pivot_eq eq x\<^sub>j in
    map (\<lambda> idx. if idx = x\<^sub>i_idx then 
                    eq'
                else
                    subst_var_eq x\<^sub>j (rhs eq') (t ! idx)
        ) [0..<length t]"

definition pivot' :: "var \<Rightarrow> var \<Rightarrow> 'a::lrv state \<Rightarrow> 'a state" where
  "pivot' x\<^sub>i x\<^sub>j s \<equiv> s\<lparr> \<T> := pivot_tableau' x\<^sub>i x\<^sub>j (\<T> s) \<rparr>"
(*>*)
text{* \noindent Then, the next implementation of @{text pivot} satisfies its specification: *}
(*<*)
definition pivot_tableau :: "var \<Rightarrow> var \<Rightarrow> tableau \<Rightarrow> tableau" where
(*>*)
"pivot_tableau x\<^sub>i x\<^sub>j t \<equiv> let eq = eq_for_lvar t x\<^sub>i; eq' = pivot_eq eq x\<^sub>j in
    map (\<lambda> e. if lhs e = lhs eq then eq' else subst_var_eq x\<^sub>j (rhs eq') e) t"

(*<*)
definition pivot :: "var \<Rightarrow> var \<Rightarrow> 'a::lrv state \<Rightarrow> 'a state" where
(*>*)
"pivot x\<^sub>i x\<^sub>j s \<equiv> s\<lparr> \<T> := pivot_tableau x\<^sub>i x\<^sub>j (\<T> s) \<rparr>"
(*<*)
(* TODO: Move to Auxiliary.thy *)
lemma map_reindex:
  assumes "\<forall> i < length l. g (l ! i) = f i"
  shows "map f [0..<length l] = map g l"
using assms
by (induct l rule: rev_induct) (auto simp add: nth_append split: if_splits)

lemma pivot'pivot:
  assumes "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)"
  shows "pivot' x\<^sub>i x\<^sub>j s = pivot x\<^sub>i x\<^sub>j s"
proof-
  have "\<And> t. \<lbrakk>\<triangle> t; x\<^sub>i \<in> lvars t\<rbrakk>  \<Longrightarrow> pivot_tableau' x\<^sub>i x\<^sub>j t = pivot_tableau x\<^sub>i x\<^sub>j t"
  proof-
    fix t
    assume "\<triangle> t" "x\<^sub>i \<in> lvars t"
    let ?f = "\<lambda>idx. if idx = eq_idx_for_lvar t x\<^sub>i then pivot_eq (t ! eq_idx_for_lvar t x\<^sub>i) x\<^sub>j
            else subst_var_eq x\<^sub>j (rhs (pivot_eq (t ! eq_idx_for_lvar t x\<^sub>i) x\<^sub>j)) (t ! idx)"
    let ?f' = "\<lambda>e. if lhs e = lhs (eq_for_lvar t x\<^sub>i) then pivot_eq (eq_for_lvar t x\<^sub>i) x\<^sub>j else subst_var_eq x\<^sub>j (rhs (pivot_eq (eq_for_lvar t x\<^sub>i) x\<^sub>j)) e"
    have "\<forall> i < length t. ?f' (t ! i) = ?f i"
    proof(safe)
      fix i
      assume "i < length t"
      hence "t ! i \<in> set t" "i < length t"
        by auto
      moreover
      have "t ! eq_idx_for_lvar t x\<^sub>i \<in> set t" "eq_idx_for_lvar t x\<^sub>i < length t"
        using eq_for_lvar[of x\<^sub>i t] `x\<^sub>i \<in> lvars t` eq_idx_for_lvar[of x\<^sub>i t]
        by (auto simp add: eq_for_lvar_def)
      ultimately
      have "lhs (t ! i) = lhs (t ! eq_idx_for_lvar t x\<^sub>i) \<Longrightarrow> t ! i = t ! (eq_idx_for_lvar t x\<^sub>i)" "distinct t"
        using `\<triangle> t`
        unfolding normalized_tableau_def
        by (auto simp add: distinct_map inj_on_def)
      hence "lhs (t ! i) = lhs (t ! eq_idx_for_lvar t x\<^sub>i) \<Longrightarrow> i = eq_idx_for_lvar t x\<^sub>i"
        using `i < length t` `eq_idx_for_lvar t x\<^sub>i < length t`
        by (auto simp add: distinct_conv_nth)
      thus "?f' (t ! i) = ?f i"
        by (auto simp add: eq_for_lvar_def)
    qed
    thus "pivot_tableau' x\<^sub>i x\<^sub>j t = pivot_tableau x\<^sub>i x\<^sub>j t"
      unfolding pivot_tableau'_def pivot_tableau_def
      unfolding Let_def
      by (auto simp add: map_reindex)
  qed
  thus ?thesis
    using assms
    unfolding pivot_def pivot'_def
    by simp
qed
end
(*>*)
(*<*)
sublocale Pivot' < Pivot eq_idx_for_lvar pivot
proof
  fix s::"'a state" and x\<^sub>i x\<^sub>j and v::"'a valuation"
  assume "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
  show "let s' = pivot x\<^sub>i x\<^sub>j s in \<V> s' = \<V> s \<and> \<B> s' = \<B> s \<and> \<U> s' = \<U> s"
    unfolding pivot_def
    by (auto simp add: Let_def)

  let ?t = "\<T> s"
  let ?idx = "eq_idx_for_lvar ?t x\<^sub>i"
  let ?eq = "?t ! ?idx"
  let ?eq' = "pivot_eq ?eq x\<^sub>j"

  have "?idx < length ?t" "lhs (?t ! ?idx) = x\<^sub>i"
    using `x\<^sub>i \<in> lvars ?t`
    using eq_idx_for_lvar
    by auto
  
  have "distinct (map lhs ?t)"
    using `\<triangle> ?t`
    unfolding normalized_tableau_def
    by simp

  have "x\<^sub>j \<in> rvars_eq ?eq"
    using `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)`
    unfolding eq_for_lvar_def
    by simp
  hence "x\<^sub>j \<in> rvars ?t"
    using `?idx < length ?t`
    using in_set_conv_nth[of ?eq ?t]
    by (auto simp add: rvars_def)
  hence "x\<^sub>j \<notin> lvars ?t"
    using `\<triangle> ?t`
    unfolding normalized_tableau_def
    by auto
  
  have "x\<^sub>i \<notin> rvars ?t"
    using `x\<^sub>i \<in> lvars ?t` `\<triangle> ?t`
    unfolding normalized_tableau_def rvars_def
    by auto
  hence "x\<^sub>i \<notin> rvars_eq ?eq"
    unfolding rvars_def
    using `?idx < length ?t`
    using in_set_conv_nth[of ?eq ?t]
    by auto

  have "x\<^sub>i \<noteq> x\<^sub>j"
    using `x\<^sub>j \<in> rvars_eq ?eq`  `x\<^sub>i \<notin> rvars_eq ?eq` 
    by auto

  have "?eq' = (x\<^sub>j, rhs ?eq')"
    using lhs_pivot_eq[of x\<^sub>j ?eq]
    using `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)` `lhs (?t ! ?idx) = x\<^sub>i` `x\<^sub>i \<notin> rvars_eq ?eq`
    by (auto simp add: eq_for_lvar_def) (cases "?eq'", simp)+

  let ?I1 = "[0..<?idx]" 
  let ?I2 = "[?idx + 1..<length ?t]"
  have "[0..<length ?t] = ?I1 @ [?idx] @ ?I2"
    using `?idx < length ?t`
    by (rule interval_3split)
  hence map_lhs_pivot: 
    "map lhs (\<T> (pivot' x\<^sub>i x\<^sub>j s)) = 
     map (\<lambda>idx. lhs (?t ! idx)) ?I1 @ [x\<^sub>j] @ map (\<lambda>idx. lhs (?t ! idx)) ?I2"
    using `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)` `lhs (?t ! ?idx) = x\<^sub>i` `x\<^sub>i \<notin> rvars_eq ?eq`
    by (auto simp add: Let_def subst_var_eq_def eq_for_lvar_def lhs_pivot_eq pivot'_def pivot_tableau'_def)
  
  have lvars_pivot: "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
        lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  proof-
    have "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =  
          {x\<^sub>j} \<union> (\<lambda>idx. lhs (?t ! idx)) ` ({0..<length?t} - {?idx})"
      using `?idx < length ?t` `?eq' = (x\<^sub>j, rhs ?eq')`
      by (cases ?eq', auto simp add: Let_def pivot'_def pivot_tableau'_def lvars_def subst_var_eq_def)+
    also have "... = {x\<^sub>j} \<union> (((\<lambda>idx. lhs (?t ! idx)) ` {0..<length?t}) - {lhs (?t ! ?idx)})"
      using `?idx < length ?t` `distinct (map lhs ?t)`
      by (auto simp add: distinct_conv_nth)
    also have "... = {x\<^sub>j} \<union> (set (map lhs ?t) - {x\<^sub>i})"
      using `lhs (?t ! ?idx) = x\<^sub>i`
      by (auto simp add: in_set_conv_nth rev_image_eqI) (auto simp add: image_def)
    finally show "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) = 
      lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
      by (simp add: lvars_def)
  qed
  moreover
  have rvars_pivot: "rvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
        rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
  proof-
    have "rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})"
      using rvars_pivot_eq[of x\<^sub>j ?eq]
      using `lhs (?t ! ?idx) = x\<^sub>i`
      using `x\<^sub>j \<in> rvars_eq ?eq` `x\<^sub>i \<notin> rvars_eq ?eq`
      by simp
      
    let ?S1 = "rvars_eq ?eq'"
    let ?S2 = "\<Union>idx\<in>({0..<length ?t} - {?idx}). 
                  rvars_eq (subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx))"

    have "rvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) = ?S1 \<union> ?S2"
      unfolding pivot'_def pivot_tableau'_def rvars_def
      using `?idx < length ?t`
      by (auto simp add: Let_def split: if_splits)
    also have "... = {x\<^sub>i} \<union> (rvars ?t - {x\<^sub>j})" (is "?S1 \<union> ?S2 = ?rhs")
    proof
      show "?S1 \<union> ?S2 \<subseteq> ?rhs"
      proof-
        have "?S1 \<subseteq> ?rhs"
          using `?idx < length ?t`
          unfolding rvars_def
          using `rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})`
          by (force simp add: in_set_conv_nth)
        moreover
        have "?S2 \<subseteq> ?rhs"
        proof-
          have "?S2 \<subseteq> (\<Union>idx\<in>{0..<length ?t}. (rvars_eq (?t ! idx) - {x\<^sub>j}) \<union> rvars_eq ?eq')"
            apply (rule UN_mono)
            using rvars_eq_subst_var_eq 
            by auto
          also have "... \<subseteq> rvars_eq ?eq' \<union> (\<Union>idx\<in>{0..<length ?t}. rvars_eq (?t ! idx) - {x\<^sub>j})"
            by auto
          also have "... = rvars_eq ?eq' \<union> (rvars ?t - {x\<^sub>j})"
            unfolding rvars_def
            by (force simp add: in_set_conv_nth)
          finally show ?thesis
            using `rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})`
            unfolding rvars_def
            using `?idx < length ?t`
            by auto
        qed
        ultimately
        show ?thesis
          by simp
      qed
    next
      show "?rhs \<subseteq> ?S1 \<union> ?S2"
      proof
        fix x
        assume "x \<in> ?rhs"
        show "x \<in> ?S1 \<union> ?S2"
        proof (cases "x \<in> rvars_eq ?eq'")
          case True
          thus ?thesis
            by auto
        next
          case False
          let ?S2'  = "\<Union>idx\<in>({0..<length ?t} - {?idx}). 
                        (rvars_eq (?t ! idx) - {x\<^sub>j}) - rvars_eq ?eq'"
          have "x \<in> ?S2'"
            using False `x \<in> ?rhs`
            using `rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})`
            unfolding rvars_def
            by (force simp add: in_set_conv_nth)
          moreover
          have "?S2 \<supseteq> ?S2'"
            apply (rule UN_mono)
            using rvars_eq_subst_var_eq_supset[of _ x\<^sub>j "rhs ?eq'" ]
            by auto
          ultimately
          show ?thesis
            by auto
        qed
      qed
    qed
    ultimately
    show ?thesis
      by simp
  qed
  ultimately
  show "let s' = pivot x\<^sub>i x\<^sub>j s in rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i} \<and> lvars (\<T> s') = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
    using pivot'pivot
    using `\<triangle> (\<T> s)` `x\<^sub>i \<in> lvars (\<T> s)`
    by (simp add: Let_def)
  have "\<triangle> (\<T> (pivot' x\<^sub>i x\<^sub>j s))"
    unfolding normalized_tableau_def
  proof
    show "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) \<inter>
          rvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) = {}"
      using `\<triangle> (\<T> s)`
      unfolding normalized_tableau_def
      using lvars_pivot rvars_pivot
      using `x\<^sub>i \<noteq> x\<^sub>j`
      by auto

    show "distinct (map lhs (\<T> (pivot' x\<^sub>i x\<^sub>j s)))"
      using map_parametrize_idx[of lhs ?t]
      using map_lhs_pivot
      using `distinct (map lhs ?t)`
      using interval_3split[of ?idx "length ?t"] `?idx < length ?t`
      using `x\<^sub>j \<notin> lvars ?t`
      unfolding lvars_def
      by auto
  qed
  moreover
  have "v \<Turnstile>\<^sub>t ?t = v \<Turnstile>\<^sub>t \<T> (pivot' x\<^sub>i x\<^sub>j s)"
    unfolding satisfies_tableau_def
  proof
    assume "\<forall>e\<in>set (?t). v \<Turnstile>\<^sub>e e"
    show "\<forall>e\<in>set (\<T> (pivot' x\<^sub>i x\<^sub>j s)). v \<Turnstile>\<^sub>e e"
    proof-
      have "v \<Turnstile>\<^sub>e ?eq'"
        using `x\<^sub>i \<notin> rvars_eq ?eq`
        using `?idx < length ?t` `\<forall>e\<in>set (?t). v \<Turnstile>\<^sub>e e`
        using `x\<^sub>j \<in> rvars_eq ?eq` `x\<^sub>i \<in> lvars ?t`
        by (simp add: equiv_pivot_eq eq_idx_for_lvar)
      moreover
      { 
        fix idx
        assume "idx < length ?t" "idx \<noteq> ?idx"

        have "v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx)"
          using `?eq' = (x\<^sub>j, rhs ?eq')`
          using `v \<Turnstile>\<^sub>e ?eq'` `idx < length ?t` `\<forall>e\<in>set (?t). v \<Turnstile>\<^sub>e e`
          using equiv_subst_var_eq[of v x\<^sub>j "rhs ?eq'" "?t ! idx"]
          by auto
      }
      ultimately
      show ?thesis
        by (auto simp add: pivot'_def pivot_tableau'_def Let_def)
    qed
  next
    assume "\<forall>e\<in>set (\<T> (pivot' x\<^sub>i x\<^sub>j s)). v \<Turnstile>\<^sub>e e"
    hence "v \<Turnstile>\<^sub>e ?eq'"
          "\<And> idx. \<lbrakk>idx < length ?t; idx \<noteq> ?idx \<rbrakk> \<Longrightarrow> v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx)"
      using `?idx < length ?t`
      unfolding pivot'_def pivot_tableau'_def
      by (auto simp add: Let_def)

    show "\<forall>e\<in>set (\<T> s). v \<Turnstile>\<^sub>e e"
    proof-
      {
        fix idx
        assume "idx < length ?t"
        have "v \<Turnstile>\<^sub>e (?t ! idx)"
        proof (cases "idx = ?idx")
          case True
          thus ?thesis
            using `v \<Turnstile>\<^sub>e ?eq'`
            using `x\<^sub>j \<in> rvars_eq ?eq` `x\<^sub>i \<in> lvars ?t` `x\<^sub>i \<notin> rvars_eq ?eq`
            by (simp add: eq_idx_for_lvar equiv_pivot_eq)
        next
          case False
          thus ?thesis
            using `idx < length ?t`
            using `\<lbrakk>idx < length ?t; idx \<noteq> ?idx \<rbrakk> \<Longrightarrow> v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx)`
            using `v \<Turnstile>\<^sub>e ?eq'` `?eq' = (x\<^sub>j, rhs ?eq')`
            using equiv_subst_var_eq[of v x\<^sub>j "rhs ?eq'" "?t ! idx"]
            by auto
        qed
      }
      thus ?thesis
        by (force simp add: in_set_conv_nth)
    qed
  qed
  ultimately
  show "let s' = pivot x\<^sub>i x\<^sub>j s in v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s' \<and> \<triangle> (\<T> s')"
    using pivot'pivot
    using `\<triangle> (\<T> s)` `x\<^sub>i \<in> lvars (\<T> s)`
    by (simp add: Let_def)
qed

(*>*)
subsection{* Check implementation *}

text{* The @{text check} function is called when all rhs variables are
in bounds, and it checks if there is a lhs variable that is not. If
there is no such variable, then satisfiability is detected and @{text
"check"} succeeds. If there is a lhs variable @{text "x\<^sub>i"} out of its
bounds, a rhs variable @{text "x\<^sub>j"} is sought which allows pivoting
with @{text "x\<^sub>i"} and updating @{text "x\<^sub>i"} to its violated bound. If
@{text "x\<^sub>i"} is under its lower bound it must be increased, and if
@{text "x\<^sub>j"} has a positive coefficient it must be increased so it
must be under its upper bound and if it has a negative coefficient it
must be decreased so it must be above its lower bound. The case when
@{text "x\<^sub>i"} is above its upper bound is symmetric (avoiding
symmetries is discussed in Section \ref{sec:symmetries}). If there is
no such @{text "x\<^sub>j"}, unsatisfiability is detected and @{text "check"}
fails. The procedure is recursively repeated, until it either succeeds
or fails. To ensure termination, variables @{text "x\<^sub>i"} and @{text
"x\<^sub>j"} must be chosen with respect to a fixed variable ordering. For
choosing these variables auxiliary functions @{text
"min_lvar_not_in_bounds"}, @{text "min_rvar_inc"} and @{text
"min_rvar_dec"} are specified (each in its own locale). For, example:
*}

locale MinLVarNotInBounds = fixes min_lvar_not_in_bounds::"'a::lrv state \<Rightarrow> var option"
assumes 

(*<*)min_lvar_not_in_bounds_None: (*>*)"min_lvar_not_in_bounds s = None \<longrightarrow> (\<forall>x\<in>lvars (\<T> s). in_bounds x \<langle>\<V> s\<rangle> (\<B> s))" (*<*)and(*>*)

(*<*)min_lvar_not_in_bounds_Some': (*>*)"min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> x\<^sub>i\<in>lvars (\<T> s) \<and> \<not>in_bounds x\<^sub>i \<langle>\<V> s\<rangle> (\<B> s) 
    \<and> (\<forall>x\<in>lvars (\<T> s). x < x\<^sub>i \<longrightarrow> in_bounds x \<langle>\<V> s\<rangle> (\<B> s))"
(*<*)
begin
lemma min_lvar_not_in_bounds_None':
  "min_lvar_not_in_bounds s = None \<longrightarrow> (\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>b \<B> s \<parallel> lvars (\<T> s))"
  unfolding satisfies_bounds_set.simps
  by (rule min_lvar_not_in_bounds_None)

lemma min_lvar_not_in_bounds_lvars:"min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> x\<^sub>i \<in> lvars (\<T> s)"
  using min_lvar_not_in_bounds_Some'
  by simp

lemma min_lvar_not_in_bounds_Some: "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> \<not> in_bounds x\<^sub>i \<langle>\<V> s\<rangle> (\<B> s)"
  using min_lvar_not_in_bounds_Some'
  by simp


lemma min_lvar_not_in_bounds_Some_min: "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow>  (\<forall> x \<in> lvars (\<T> s). x < x\<^sub>i \<longrightarrow> in_bounds x \<langle>\<V> s\<rangle> (\<B> s))"
  using min_lvar_not_in_bounds_Some'
  by simp

end
(*>*)
(*<*)
abbreviation reasable_var where
"reasable_var dir x eq s \<equiv> 
   (coeff (rhs eq) x > 0 \<and> \<lhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x)) \<or>
   (coeff (rhs eq) x < 0 \<and> \<rhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x))"
(*>*)
(*<*)
locale MinRVarsEq = 
fixes min_rvar_incdec_eq :: "'a Direction \<Rightarrow> 'a::lrv state \<Rightarrow> eq \<Rightarrow> var option"
assumes min_rvar_incdec_eq_None:
  "min_rvar_incdec_eq dir s eq = None \<longrightarrow> 
      (\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s)"
assumes min_rvar_incdec_eq_Some_rvars:
  "min_rvar_incdec_eq dir s eq = Some x\<^sub>j \<longrightarrow> x\<^sub>j \<in> rvars_eq eq"
assumes min_rvar_incdec_eq_Some_incdec:
  "min_rvar_incdec_eq dir s eq = Some x\<^sub>j \<longrightarrow> reasable_var dir x\<^sub>j eq s"
assumes min_rvar_incdec_eq_Some_min:
  "min_rvar_incdec_eq dir s eq = Some x\<^sub>j \<longrightarrow> 
    (\<forall> x \<in> rvars_eq eq. x < x\<^sub>j \<longrightarrow> \<not> reasable_var dir x eq s)"
begin
lemma min_rvar_incdec_eq_None':
  assumes *: "dir = Positive \<or> dir = Negative"
  shows "min_rvar_incdec_eq dir s eq = None \<longrightarrow> 
      v \<Turnstile>\<^sub>b \<B> s \<longrightarrow> le (lt dir) ((rhs eq) \<lbrace>v\<rbrace>) ((rhs eq) \<lbrace>\<langle>\<V> s\<rangle>\<rbrace>)"
proof (rule impI)+
  assume "min_rvar_incdec_eq dir s eq = None" "v \<Turnstile>\<^sub>b \<B> s"
  have "\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s"
    using `min_rvar_incdec_eq dir s eq = None`
    using min_rvar_incdec_eq_None
    by simp
  
  have "\<forall> x \<in> rvars_eq eq. (0 < coeff (rhs eq) x \<longrightarrow> le (lt dir) 0 (\<langle>\<V> s\<rangle> x - v x)) \<and> (coeff (rhs eq) x < 0 \<longrightarrow> le (lt dir) (\<langle>\<V> s\<rangle> x - v x) 0)"
  proof (safe)
    fix x
    assume "x \<in> rvars_eq eq" "0 < coeff (rhs eq) x" "0 \<noteq> \<langle>\<V> s\<rangle> x - v x"
    hence "\<not> (\<lhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x))"
      using `\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s`
      by auto
    hence "\<unrhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x)"
      using *
      by (cases "UB dir s x") (auto simp add: bound_compare_defs)
    moreover
    have "\<unlhd>\<^sub>u\<^sub>b (lt dir) (v x) (UB dir s x)"
      using `v \<Turnstile>\<^sub>b \<B> s` *
      unfolding satisfies_bounds.simps
      by (auto simp add: bound_compare''_defs)
    ultimately
    have "le (lt dir) (v x) (\<langle>\<V> s\<rangle> x)"
      using *
      by (cases "UB dir s x") (auto simp add: bound_compare_defs)
    thus "lt dir 0 (\<langle>\<V> s\<rangle> x - v x)"
      using `0 \<noteq> \<langle>\<V> s\<rangle> x - v x` *
      using minus_gt[of "v x" "\<langle>\<V> s\<rangle> x"] minus_lt[of "\<langle>\<V> s\<rangle> x" "v x"]
      by auto
  next
    fix x
    assume "x \<in> rvars_eq eq" "0 > coeff (rhs eq) x" "\<langle>\<V> s\<rangle> x - v x \<noteq> 0"
    hence "\<not> (\<rhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x))"
      using `\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s`
      by auto
    hence "\<unlhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x)"
      using *
      by (cases "LB dir s x") (auto simp add: bound_compare_defs)
    moreover
    have "\<unrhd>\<^sub>l\<^sub>b (lt dir) (v x) (LB dir s x)"
      using `v \<Turnstile>\<^sub>b \<B> s` *
      unfolding satisfies_bounds.simps
      by (auto simp add: bound_compare''_defs)
    ultimately
    have "le (lt dir) (\<langle>\<V> s\<rangle> x) (v x)"
      using *
      by (cases "LB dir s x") (auto simp add: bound_compare_defs)
    thus "lt dir (\<langle>\<V> s\<rangle> x - v x) 0"
      using `\<langle>\<V> s\<rangle> x - v x \<noteq> 0` *
      using minus_lt[of "\<langle>\<V> s\<rangle> x" "v x"] minus_gt[of "v x" "\<langle>\<V> s\<rangle> x"]
      by auto
  qed
  hence "le (lt dir) 0 (rhs eq \<lbrace> \<lambda> x. \<langle>\<V> s\<rangle> x - v x\<rbrace>)"
    using *
    apply auto
    using valuate_nonneg[of "rhs eq" "\<lambda>x. \<langle>\<V> s\<rangle> x - v x"]
    apply force
    using valuate_nonpos[of "rhs eq" "\<lambda>x. \<langle>\<V> s\<rangle> x - v x"]
    apply force
    done
  thus "le (lt dir) rhs eq \<lbrace> v \<rbrace> rhs eq \<lbrace> \<langle>\<V> s\<rangle> \<rbrace>"
    using `dir = Positive \<or> dir = Negative`
    using minus_gt[of "rhs eq \<lbrace> v \<rbrace>" "rhs eq \<lbrace> \<langle>\<V> s\<rangle> \<rbrace>"]
    by (auto simp add: valuate_diff[THEN sym])
qed
end
(*>*)
(*<*)
locale MinRVars = EqForLVar + MinRVarsEq
begin
  abbreviation min_rvar_incdec :: "'a Direction \<Rightarrow> 'a::lrv state \<Rightarrow> var \<Rightarrow> var option" where
  "min_rvar_incdec dir s x\<^sub>i \<equiv> min_rvar_incdec_eq dir s (eq_for_lvar (\<T> s) x\<^sub>i)"
end
(*>*)
(*<*)
locale MinVars = MinLVarNotInBounds + MinRVars
(*>*)

(*<*)
locale PivotUpdateMinVars = 
  PivotAndUpdate eq_idx_for_lvar pivot_and_update + 
  MinVars min_lvar_not_in_bounds eq_idx_for_lvar min_rvar_incdec_eq for
  eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat" and
  min_lvar_not_in_bounds :: "'a::lrv state \<Rightarrow> var option" and
  min_rvar_incdec_eq :: "'a Direction \<Rightarrow> 'a state \<Rightarrow> eq \<Rightarrow> var option" and
  pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> 'a state \<Rightarrow> 'a state"
(*>*)
(*<*)
begin
(*>*)
(*<*)
definition check' where
"check' dir x\<^sub>i s \<equiv> 
     let l\<^sub>i = the (LB dir s x\<^sub>i);
         x\<^sub>j' = min_rvar_incdec dir s x\<^sub>i 
     in case x\<^sub>j' of 
           None \<Rightarrow> s \<lparr> \<U> := True \<rparr>
         | Some x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s"

lemma check'_cases:
 assumes "\<lbrakk>min_rvar_incdec dir s x\<^sub>i = None; check' dir x\<^sub>i s = s\<lparr> \<U> := True \<rparr>\<rbrakk> \<Longrightarrow> P (s\<lparr>\<U> := True\<rparr>)"
 assumes "\<And> x\<^sub>j l\<^sub>i. \<lbrakk>min_rvar_incdec dir s x\<^sub>i = Some x\<^sub>j;
           l\<^sub>i = the (LB dir s x\<^sub>i);
           check' dir x\<^sub>i s = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s\<rbrakk> \<Longrightarrow> 
        P (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
 shows "P (check' dir x\<^sub>i s)"
using assms
unfolding check'_def
by (cases "min_rvar_incdec dir s x\<^sub>i") auto

partial_function (tailrec) check where
 "check s = 
    (if \<U> s then s
     else let x\<^sub>i' = min_lvar_not_in_bounds s 
          in case x\<^sub>i' of 
               None \<Rightarrow> s
             | Some x\<^sub>i \<Rightarrow> let dir = if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive
                                    else Negative 
                          in check (check' dir x\<^sub>i s))"
declare check.simps[code]

inductive check_dom where
step: "\<lbrakk>\<And>x\<^sub>i. \<lbrakk>\<not> \<U> s; Some x\<^sub>i = min_lvar_not_in_bounds s; \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i\<rbrakk>
     \<Longrightarrow> check_dom (check' Positive x\<^sub>i s);
  \<And>x\<^sub>i. \<lbrakk>\<not> \<U> s; Some x\<^sub>i = min_lvar_not_in_bounds s; \<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i\<rbrakk>
     \<Longrightarrow> check_dom (check' Negative x\<^sub>i s)\<rbrakk>
\<Longrightarrow> check_dom s"

(*>*)

text{*
The definition of @{text check} can be given by:

@{text[display]
"check s \<equiv> if \<U> s then s
            else let x\<^sub>i' = min_lvar_not_in_bounds s in 
                 case x\<^sub>i' of  None \<Rightarrow> s
                           | Some x\<^sub>i \<Rightarrow> if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then check (check_inc x\<^sub>i s)
                                           else check (check_dec x\<^sub>i s)"
}

@{text[display]
"check_inc x\<^sub>i s \<equiv> let l\<^sub>i = the (\<B>\<^sub>l s x\<^sub>i); x\<^sub>j' = min_rvar_inc s x\<^sub>i in
   case x\<^sub>j' of None \<Rightarrow> s \<lparr> \<U> := True \<rparr> | Some x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s"
}

The definition of @{text check_dec} is analogous. It is shown (mainly
by induction) that this definition satisfies the @{text "check"}
specification. Note that this definition uses general recursion, so
its termination is non-trivial. It has been shown that it terminates
for all states satisfying the check preconditions. The proof is based
on the proof outline given in \cite{simplex-rad}. It is very
technically involved, but conceptually uninteresting so we do not
discuss it in more details. *}
(*<*)
lemma pivotandupdate_check_precond: 
  assumes
  "dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative)"
  "min_lvar_not_in_bounds s = Some x\<^sub>i"
  "min_rvar_incdec dir s x\<^sub>i = Some x\<^sub>j"
  "l\<^sub>i = the (LB dir s x\<^sub>i)"
  "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" " \<diamond> s"
shows "\<triangle> (\<T> (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)) \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s) \<and> \<diamond> (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s) \<and> \<nabla> (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
proof-
  have "\<B>\<^sub>l s x\<^sub>i = Some l\<^sub>i \<or> \<B>\<^sub>u s x\<^sub>i = Some l\<^sub>i"
    using `l\<^sub>i = the (LB dir s x\<^sub>i)` `dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative)`
    using `min_lvar_not_in_bounds s = Some x\<^sub>i` min_lvar_not_in_bounds_Some[of s x\<^sub>i]
    using `\<diamond> s`
    by (case_tac[!] "\<B>\<^sub>l s x\<^sub>i", case_tac[!] "\<B>\<^sub>u s x\<^sub>i") (auto simp add: bounds_consistent_def bound_compare_defs)
  thus ?thesis
    using assms
    using pivotandupdate_tableau_normalized[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    using pivotandupdate_nolhs[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    using pivotandupdate_bounds_consistent[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    using pivotandupdate_tableau_valuated[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    by (auto simp add: min_lvar_not_in_bounds_lvars  min_rvar_incdec_eq_Some_rvars)
qed
(*>*)
(*<*)
(* -------------------------------------------------------------------------- *)
(* Termination *)
(* -------------------------------------------------------------------------- *)

abbreviation gt_state' where
"gt_state' dir s s' x\<^sub>i x\<^sub>j l\<^sub>i \<equiv> 
  min_lvar_not_in_bounds s = Some x\<^sub>i \<and> 
  l\<^sub>i = the (LB dir s x\<^sub>i) \<and>
  min_rvar_incdec dir s x\<^sub>i = Some x\<^sub>j \<and>
  s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s"

definition gt_state :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" (infixl "\<succ>\<^sub>x" 100) where
 "s \<succ>\<^sub>x s' \<equiv>
   \<exists> x\<^sub>i x\<^sub>j l\<^sub>i. 
     let dir = if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative in
     gt_state' dir s s' x\<^sub>i x\<^sub>j l\<^sub>i"

abbreviation succ :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" (infixl "\<succ>" 100) where
"s \<succ> s' \<equiv> \<triangle> (\<T> s) \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> \<nabla> s \<and> s \<succ>\<^sub>x s'"

abbreviation succ_rel :: "'a state rel" where
"succ_rel \<equiv> {(s, s'). s \<succ> s'}"

abbreviation succ_rel_trancl :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" (infixl "\<succ>\<^sup>+" 100) where
"s \<succ>\<^sup>+ s' \<equiv> (s, s') \<in> succ_rel\<^sup>+"

abbreviation succ_rel_rtrancl :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" (infixl "\<succ>\<^sup>*" 100) where
"s \<succ>\<^sup>* s' \<equiv> (s, s') \<in> succ_rel\<^sup>*"

lemma succ_vars:
  assumes "s \<succ> s'"
  obtains x\<^sub>i x\<^sub>j where
  "x\<^sub>i \<in> lvars (\<T> s)"
  "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i" "x\<^sub>j \<in> rvars (\<T> s)"
  "lvars (\<T> s') = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
proof-
  from assms
  obtain x\<^sub>i x\<^sub>j c
    where *:
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  hence
    "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
    "lvars (\<T> s') =  lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
    "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j]
    using pivotandupdate_lvars[of s x\<^sub>i x\<^sub>j]
    by auto
  moreover
  have "x\<^sub>j \<in> rvars (\<T> s)"
    using `x\<^sub>i \<in> lvars (\<T> s)`
    using `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)`
    using eq_for_lvar[of x\<^sub>i "\<T> s"]
    unfolding rvars_def
    by auto
  ultimately
  have
  "x\<^sub>i \<in> lvars (\<T> s)"
  "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i" "x\<^sub>j \<in> rvars (\<T> s)"
  "lvars (\<T> s') = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
    by auto
  thus thesis
    ..
qed

lemma succ_vars_id:
  assumes "s \<succ> s'"
  shows "lvars (\<T> s) \<union> rvars (\<T> s) = 
         lvars (\<T> s') \<union> rvars (\<T> s')"
using assms
by (rule succ_vars) auto

lemma succ_inv:
  assumes "s \<succ> s'"
  shows "\<triangle> (\<T> s')" "\<nabla> s'" "\<diamond> s'" "\<B> s = \<B> s'"
  "(v::'a valuation) \<Turnstile>\<^sub>t (\<T> s) \<longleftrightarrow> v \<Turnstile>\<^sub>t (\<T> s')"
proof-
  from assms obtain x\<^sub>i x\<^sub>j c
    where *:
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  thus  "\<triangle> (\<T> s')" "\<nabla> s'" "\<diamond> s'" "\<B> s = \<B> s'"
    "(v::'a valuation) \<Turnstile>\<^sub>t (\<T> s) \<longleftrightarrow> v \<Turnstile>\<^sub>t (\<T> s')"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using pivotandupdate_tableau_normalized[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_bounds_consistent[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_bounds_id[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_tableau_equiv
    using pivotandupdate_tableau_valuated
    by auto
qed

lemma succ_rvar_valuation_id:
  assumes "s \<succ> s'" "x \<in> rvars (\<T> s)" "x \<in> rvars (\<T> s')"
  shows "\<langle>\<V> s\<rangle> x = \<langle>\<V> s'\<rangle> x"
proof-
  from assms obtain x\<^sub>i x\<^sub>j c
    where *:
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  thus ?thesis
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using `x \<in> rvars (\<T> s)` `x \<in> rvars (\<T> s')`
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j x c]
    by (force simp add: normalized_tableau_def map2fun_def)
qed

lemma succ_min_lvar_not_in_bounds:
  assumes "s \<succ> s'" 
  "xr \<in> lvars (\<T> s)" "xr \<in> rvars (\<T> s')"
  shows "\<not> in_bounds xr (\<langle>\<V> s\<rangle>) (\<B> s)"
  "\<forall> x \<in> lvars (\<T> s). x < xr \<longrightarrow> in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s)"
proof-
  from assms obtain x\<^sub>i x\<^sub>j c
    where *:
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  hence "x\<^sub>i = xr"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using `xr \<in> lvars (\<T> s)` `xr \<in> rvars (\<T> s')`
    using pivotandupdate_rvars
    by (auto simp add: normalized_tableau_def)
  thus "\<not> in_bounds xr (\<langle>\<V> s\<rangle>) (\<B> s)"
       "\<forall> x \<in> lvars (\<T> s). x < xr \<longrightarrow> in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s)"
    using `min_lvar_not_in_bounds s = Some x\<^sub>i`
    using min_lvar_not_in_bounds_Some min_lvar_not_in_bounds_Some_min
    by simp_all
qed

lemma succ_min_rvar:
  assumes "s \<succ> s'" 
  "xs \<in> lvars (\<T> s)" "xs \<in> rvars (\<T> s')"
  "xr \<in> rvars (\<T> s)" "xr \<in> lvars (\<T> s')"
  "eq = eq_for_lvar (\<T> s) xs" and
  dir: "dir = Positive \<or> dir = Negative"
  shows 
   "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs) \<longrightarrow> 
             reasable_var dir xr eq s \<and> (\<forall> x \<in> rvars_eq eq. x < xr \<longrightarrow> \<not> reasable_var dir x eq s)"
proof-
  from assms(1) obtain x\<^sub>i x\<^sub>j c
    where"\<triangle> (\<T> s) \<and> \<nabla> s \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" 
    "gt_state' (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative) s s' x\<^sub>i x\<^sub>j c"
    by (auto simp add: gt_state_def Let_def)
  hence
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j c s" and
    *: "(\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i \<and> min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j) \<or> 
        (\<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i \<and> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j)"
    by (auto split: if_splits)

  hence "xr = x\<^sub>j" "xs = x\<^sub>i"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using `xr \<in> rvars (\<T> s)` `xr \<in> lvars (\<T> s')`
    using `xs \<in> lvars (\<T> s)` `xs \<in> rvars (\<T> s')`
    using pivotandupdate_lvars pivotandupdate_rvars
    by (auto simp add: normalized_tableau_def)
  show "\<not> (\<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs)) \<longrightarrow> 
            reasable_var dir xr eq s \<and> (\<forall> x \<in> rvars_eq eq. x < xr \<longrightarrow> \<not> reasable_var dir x eq s)"
  proof
    assume "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs)"
    hence "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs)"
      using dir
      by (cases "LB dir s xs") (auto simp add: bound_compare_defs)
    moreover
    hence "\<not> (\<rhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (UB dir s xs))"
      using `\<diamond> s` dir
      using bounds_consistent_gt_ub bounds_consistent_lt_lb
      by (force simp add:  bound_compare''_defs)
    ultimately
    have "min_rvar_incdec dir s xs = Some xr"
      using * `xr = x\<^sub>j` `xs = x\<^sub>i` dir
      by (auto simp add: bound_compare''_defs)
    thus "reasable_var dir xr eq s \<and> (\<forall> x \<in> rvars_eq eq. x < xr \<longrightarrow> \<not> reasable_var dir x eq s)"
      using `eq = eq_for_lvar (\<T> s) xs`
      using min_rvar_incdec_eq_Some_min[of dir s eq xr]
      using min_rvar_incdec_eq_Some_incdec[of dir s eq xr]
      by simp
  qed
qed

lemma succ_set_on_bound:
  assumes 
  "s \<succ> s'" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<in> rvars (\<T> s')" and
  dir: "dir = Positive \<or> dir = Negative"
  shows 
  "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i) \<longrightarrow> \<langle>\<V> s'\<rangle> x\<^sub>i = the (LB dir s x\<^sub>i)"
  "\<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>l s x\<^sub>i) \<or> \<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>u s x\<^sub>i)"
proof-
  from assms(1) obtain x\<^sub>i' x\<^sub>j c
    where"\<triangle> (\<T> s) \<and> \<nabla> s \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" 
    "gt_state' (if \<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i' then Positive else Negative) s s' x\<^sub>i' x\<^sub>j c"
    by (auto simp add: gt_state_def Let_def)
  hence
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i'"
    "s' = pivot_and_update x\<^sub>i' x\<^sub>j c s" and
    *: "(\<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i' \<and> c = the (\<B>\<^sub>l s x\<^sub>i') \<and> min_rvar_incdec Positive s x\<^sub>i' = Some x\<^sub>j) \<or> 
        (\<not> \<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i' \<and> c = the (\<B>\<^sub>u s x\<^sub>i') \<and> min_rvar_incdec Negative s x\<^sub>i' = Some x\<^sub>j)"
    by (auto split: if_splits)
  hence "x\<^sub>i = x\<^sub>i'" "x\<^sub>i' \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i')"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i']
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i'" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i'" x\<^sub>j]
    using `x\<^sub>i \<in> lvars (\<T> s)` `x\<^sub>i \<in> rvars (\<T> s')`
    using pivotandupdate_rvars
    by (auto simp add: normalized_tableau_def)
  show "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i) \<longrightarrow> \<langle>\<V> s'\<rangle> x\<^sub>i = the (LB dir s x\<^sub>i)"
  proof
    assume "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)"
    hence "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)"
      using dir
      by (cases "LB dir s x\<^sub>i") (auto simp add: bound_compare_defs)
    moreover
    hence "\<not> \<rhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (UB dir s x\<^sub>i)"
      using `\<diamond> s` dir
      using bounds_consistent_gt_ub bounds_consistent_lt_lb
      by (force simp add: bound_compare''_defs)
    ultimately
    show "\<langle>\<V> s'\<rangle> x\<^sub>i = the (LB dir s x\<^sub>i)"
      using * `x\<^sub>i = x\<^sub>i'` `s' = pivot_and_update x\<^sub>i' x\<^sub>j c s`
      using `\<triangle> (\<T> s)` `\<nabla> s` `x\<^sub>i' \<in> lvars (\<T> s)`
        `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i')`
      using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c] dir
      by (case_tac[!] "\<B>\<^sub>l s x\<^sub>i'", case_tac[!] "\<B>\<^sub>u s x\<^sub>i'") (auto simp add: bound_compare_defs map2fun_def)
  qed

  have "\<not> \<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i'  \<longrightarrow> \<langle>\<V> s\<rangle> x\<^sub>i' >\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i'"
    using `min_lvar_not_in_bounds s = Some x\<^sub>i'`
    using min_lvar_not_in_bounds_Some[of s x\<^sub>i']
    using not_in_bounds[of x\<^sub>i' "\<langle>\<V> s\<rangle>" "\<B>\<^sub>l s" "\<B>\<^sub>u s"]
    by auto
  thus "\<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>l s x\<^sub>i) \<or> \<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>u s x\<^sub>i)"
    using `\<triangle> (\<T> s)` `\<nabla> s` `x\<^sub>i' \<in> lvars (\<T> s)`
        `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i')`
    using `s' = pivot_and_update x\<^sub>i' x\<^sub>j c s` `x\<^sub>i = x\<^sub>i'`
    using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c]
    using *
    by (case_tac[!] "\<B>\<^sub>l s x\<^sub>i'", case_tac[!] "\<B>\<^sub>u s x\<^sub>i'") (auto simp add: map2fun_def bound_compare_defs)
qed

lemma succ_rvar_valuation:
  assumes
  "s \<succ> s'" "x \<in> rvars (\<T> s')"
  shows
  "\<langle>\<V> s'\<rangle> x = \<langle>\<V> s\<rangle> x \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>l s x) \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>u s x)"
proof-
  from assms
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j"
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  hence
    "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<notin> rvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
    "x\<^sub>j \<in> rvars (\<T> s)" "x\<^sub>j \<notin> lvars (\<T> s)" "x\<^sub>i \<noteq> x\<^sub>j"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using rvars_of_lvar_rvars `\<triangle> (\<T> s)`
    by (auto simp add: normalized_tableau_def)
  hence
    "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
    "x \<in> rvars (\<T> s) \<or> x = x\<^sub>i" "x \<noteq> x\<^sub>j" "x \<noteq> x\<^sub>i \<longrightarrow> x \<notin> lvars (\<T> s)"
    using `x \<in> rvars (\<T> s')`
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j]
    using `\<triangle> (\<T> s)` `\<nabla> s` `s' = pivot_and_update x\<^sub>i x\<^sub>j b s`
    by (auto simp add: normalized_tableau_def)
  thus ?thesis
    using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j b]
    using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j x b]
    using `x\<^sub>i \<in> lvars (\<T> s)` `x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)`
    using `\<triangle> (\<T> s)` `\<nabla> s` `s' = pivot_and_update x\<^sub>i x\<^sub>j b s` `b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)`
    by (auto simp add: map2fun_def)
qed

lemma succ_no_vars_valuation:
  assumes 
  "s \<succ> s'" "x \<notin> tvars (\<T> s')"
  shows "look (\<V> s') x = look (\<V> s) x"
proof-
  from assms
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  hence
    "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<notin> rvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
    "x\<^sub>j \<in> rvars (\<T> s)" "x\<^sub>j \<notin> lvars (\<T> s)" "x\<^sub>i \<noteq> x\<^sub>j"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using rvars_of_lvar_rvars `\<triangle> (\<T> s)`
    by (auto simp add: normalized_tableau_def)
  thus ?thesis
    using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j x b]
    using `\<triangle> (\<T> s)` `\<nabla> s` `s' = pivot_and_update x\<^sub>i x\<^sub>j b s`
    using `x \<notin> tvars (\<T> s')`
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j]
    using pivotandupdate_lvars[of s x\<^sub>i x\<^sub>j]
    by (auto simp add: map2fun_def)
qed

lemma succ_valuation_satisfies:
  assumes "s \<succ> s'" "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
  shows "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'"
proof-
  from `s \<succ> s'`
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  hence
    "x\<^sub>i \<in> lvars (\<T> s)" 
    "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j] `\<triangle> (\<T> s)`
    by (auto simp add: normalized_tableau_def)
  thus ?thesis
    using pivotandupdate_satisfies_tableau[of s x\<^sub>i x\<^sub>j b]
    using pivotandupdate_tableau_equiv[of s x\<^sub>i x\<^sub>j ]
    using `\<triangle> (\<T> s)` `\<nabla> s` `\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s` `s' = pivot_and_update x\<^sub>i x\<^sub>j b s`
    by auto
qed

lemma succ_tableau_valuated: 
  assumes "s \<succ> s'" "\<nabla> s"
  shows "\<nabla> s'"
proof-
  from `s \<succ> s'`
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Some x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Some x\<^sub>j" 
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  hence
    "x\<^sub>i \<in> lvars (\<T> s)" 
    "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j] `\<triangle> (\<T> s)`
    by (auto simp add: normalized_tableau_def)
  thus ?thesis
    using `s' = pivot_and_update x\<^sub>i x\<^sub>j b s`
    using pivotandupdate_tableau_valuated `\<triangle> (\<T> s)` `\<nabla> s`
    by auto
qed

(* -------------------------------------------------------------------------- *)
abbreviation succ_chain where
 "succ_chain l \<equiv> rel_chain l succ_rel"

lemma succ_chain_induct:
  assumes *: "succ_chain l" "i \<le> j" "j < length l"
  assumes base: "\<And> i. P i i"
  assumes step: "\<And> i. l ! i \<succ> (l ! (i + 1)) \<Longrightarrow> P i (i + 1)"
  assumes trans: "\<And> i j k. \<lbrakk>P i j; P j k; i < j; j \<le> k\<rbrakk> \<Longrightarrow> P i k"
  shows "P i j"
using *
proof (induct "j - i" arbitrary: i)
  case 0
  thus ?case
    by (simp add: base)
next
  case (Suc k)
  have "P (i + 1) j"
    using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5)
    by auto
  moreover
  have "P i (i + 1)"
  proof (rule step)
    show "l ! i \<succ> (l ! (i + 1))"
      using Suc(2) Suc(3) Suc(5)
      unfolding rel_chain_def
      by auto
  qed
  ultimately
  show ?case
    using trans[of i "i + 1" j] Suc(2)
    by simp
qed

lemma succ_chain_bounds_id: 
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "\<B> (l ! i) = \<B> (l ! j)"
using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  thus "\<B> (l ! i) = \<B> (l ! (i + 1))"
    by (rule succ_inv(4))
qed simp_all

lemma succ_chain_vars_id': 
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "lvars (\<T> (l ! i)) \<union> rvars (\<T> (l ! i)) = 
         lvars (\<T> (l ! j)) \<union> rvars (\<T> (l ! j))"
using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  thus "tvars (\<T> (l ! i)) = tvars (\<T> (l ! (i + 1)))"
    by (rule succ_vars_id)
qed simp_all

lemma succ_chain_vars_id: 
  assumes "succ_chain l" "i < length l" "j < length l"
  shows "lvars (\<T> (l ! i)) \<union> rvars (\<T> (l ! i)) = 
         lvars (\<T> (l ! j)) \<union> rvars (\<T> (l ! j))"
proof (cases "i \<le> j")
  case True
  thus ?thesis
    using assms succ_chain_vars_id'[of l i j]
    by simp
next
  case False
  hence "j \<le> i"
    by simp
  thus ?thesis
    using assms succ_chain_vars_id'[of l j i]
    by simp
qed

lemma succ_chain_tableau_equiv':
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "(v::'a valuation) \<Turnstile>\<^sub>t \<T> (l ! i) \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (l ! j)"
using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  thus "v \<Turnstile>\<^sub>t \<T> (l ! i) = v \<Turnstile>\<^sub>t \<T> (l ! (i + 1))"
    by (rule succ_inv(5))
qed simp_all

lemma succ_chain_tableau_equiv:
  assumes "succ_chain l"  "i < length l" "j < length l"
  shows "(v::'a valuation) \<Turnstile>\<^sub>t \<T> (l ! i) \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (l ! j)"
proof (cases "i \<le> j")
  case True
  thus ?thesis
    using assms succ_chain_tableau_equiv'[of l i j v]
    by simp
next
  case False
  hence "j \<le> i"
    by auto
  thus ?thesis
    using assms succ_chain_tableau_equiv'[of l j i v]
    by simp
qed

lemma succ_chain_no_vars_valuation:
  assumes "succ_chain l"  "i \<le> j" "j < length l"
  shows "\<forall> x. x \<notin> tvars (\<T> (l ! i)) \<longrightarrow> look (\<V> (l ! i)) x = look (\<V> (l ! j)) x" (is "?P i j")
using assms
proof (induct "j - i" arbitrary: i)
  case 0
  thus ?case
    by simp
next
  case (Suc k)
  have "?P (i + 1) j"
    using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5)
    by auto
  moreover
  have "?P (i + 1) i"
  proof (rule+, rule succ_no_vars_valuation)
    show "l ! i \<succ> (l ! (i + 1))"
      using Suc(2) Suc(3) Suc(5)
      unfolding rel_chain_def
      by auto
  qed
  moreover
  have "tvars (\<T> (l ! i)) = tvars (\<T> (l ! (i + 1)))"
  proof (rule succ_vars_id)
    show "l ! i \<succ> (l ! (i + 1))"
      using Suc(2) Suc(3) Suc(5)
      unfolding rel_chain_def
      by simp
  qed
  ultimately
  show ?case
    by simp
qed

lemma succ_chain_rvar_valuation:
  assumes "succ_chain l" "i \<le> j" "j < length l" 
  shows "\<forall>x\<in>rvars (\<T> (l ! j)). 
  \<langle>\<V> (l ! j)\<rangle> x = \<langle>\<V> (l ! i)\<rangle> x \<or> 
  \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>l (l ! i) x) \<or> 
  \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>u (l ! i) x)" (is "?P i j")
using assms
proof (induct "j - i" arbitrary: j)
  case 0
  thus ?case
    by simp
next
  case (Suc k)
  have  "k = j - 1 - i" "succ_chain l" "i \<le> j - 1" "j - 1 < length l" "j > 0"
    using Suc(2) Suc(3) Suc(4) Suc(5)
    by auto
  hence ji: "?P i (j - 1)"
    using Suc(1)
    by simp

  have "l ! (j - 1) \<succ> (l ! j)"
    using Suc(3) `j < length l` `j > 0`
    unfolding rel_chain_def
    by (erule_tac x="j - 1" in allE) simp

  hence 
    jj: "?P (j - 1) j"
    using succ_rvar_valuation
    by auto

  obtain x\<^sub>i x\<^sub>j where 
    vars: "x\<^sub>i \<in> lvars (\<T> (l ! (j - 1)))" "x\<^sub>j \<in> rvars (\<T> (l ! (j - 1)))"
    "rvars (\<T> (l ! j)) = rvars (\<T> (l ! (j - 1))) - {x\<^sub>j} \<union> {x\<^sub>i}"
    using `l ! (j - 1) \<succ> (l ! j)`
    by (rule succ_vars) simp

  hence bounds:
    "\<B>\<^sub>l (l ! (j - 1)) = \<B>\<^sub>l (l ! i)" "\<B>\<^sub>l (l ! j) = \<B>\<^sub>l (l ! i)"
    "\<B>\<^sub>u (l ! (j - 1)) = \<B>\<^sub>u (l ! i)" "\<B>\<^sub>u (l ! j) = \<B>\<^sub>u (l ! i)"
    using `succ_chain l`
    using succ_chain_bounds_id[of l i "j - 1", THEN sym] `j - 1 < length l` `i \<le> j - 1`
    using succ_chain_bounds_id[of l "j - 1" j, THEN sym] `j < length l`
    by auto
  show ?case
  proof
    fix x
    assume "x \<in> rvars (\<T> (l ! j))"
    hence "x \<noteq> x\<^sub>j \<and> x \<in> rvars (\<T> (l ! (j - 1))) \<or> x = x\<^sub>i"
      using vars
      by auto
    thus "\<langle>\<V> (l ! j)\<rangle> x = \<langle>\<V> (l ! i)\<rangle> x \<or>
          \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>l (l ! i) x) \<or> 
          \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>u (l ! i) x)"
    proof
      assume "x \<noteq> x\<^sub>j \<and> x \<in> rvars (\<T> (l ! (j - 1)))"
      thus ?thesis
        using jj `x \<in> rvars (\<T> (l ! j))` ji
        using bounds
        by force
    next
      assume "x = x\<^sub>i"
      thus ?thesis
        using succ_set_on_bound(2)[of "l ! (j - 1)" "l ! j" x\<^sub>i] `l ! (j - 1) \<succ> (l ! j)`
        using vars bounds
        by auto
    qed
  qed
qed

lemma succ_chain_valuation_satisfies:
  assumes "succ_chain l"  "i \<le> j" "j < length l"
  shows "\<langle>\<V> (l ! i)\<rangle> \<Turnstile>\<^sub>t \<T> (l ! i) \<longrightarrow> \<langle>\<V> (l ! j)\<rangle> \<Turnstile>\<^sub>t \<T> (l ! j)" 
using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  thus "\<langle>\<V> (l ! i)\<rangle> \<Turnstile>\<^sub>t \<T> (l ! i) \<longrightarrow> \<langle>\<V> (l ! (i + 1))\<rangle> \<Turnstile>\<^sub>t \<T> (l ! (i + 1))"
    using succ_valuation_satisfies
    by simp
qed simp_all

lemma succ_chain_tableau_valuated:
  assumes "succ_chain l"  "i \<le> j" "j < length l"
  shows "\<nabla> (l ! i) \<longrightarrow> \<nabla> (l ! j)"
using assms
proof(rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  thus "\<nabla> (l ! i) \<longrightarrow> \<nabla> (l ! (i + 1))"
    using succ_tableau_valuated
    by auto
qed simp_all

abbreviation swap_lr where
  "swap_lr l i x \<equiv> i + 1 < length l \<and> x \<in> lvars (\<T> (l ! i)) \<and> x \<in> rvars (\<T> (l ! (i + 1)))"

abbreviation swap_rl where 
  "swap_rl l i x \<equiv> i + 1 < length l \<and> x \<in> rvars (\<T> (l ! i)) \<and> x \<in> lvars (\<T> (l ! (i + 1)))"

abbreviation always_r where
  "always_r l i j x \<equiv> \<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> x \<in> rvars (\<T> (l ! k))"

lemma succ_chain_always_r_valuation_id:
  assumes "succ_chain l" "i \<le> j" "j < length l" 
  shows "always_r l i j x \<longrightarrow> \<langle>\<V> (l ! i)\<rangle> x = \<langle>\<V> (l ! j)\<rangle> x" (is "?P i j")
using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  thus "?P i (i + 1)"
    using succ_rvar_valuation_id
    by simp
qed simp_all

lemma succ_chain_swap_rl_exists:
  assumes "succ_chain l" "i < j" "j < length l"
  "x \<in> rvars (\<T> (l ! i))" "x \<in> lvars (\<T> (l ! j))"
  shows "\<exists> k. i \<le> k \<and> k < j \<and> swap_rl l k x"
using assms
proof (induct "j - i" arbitrary: i)
  case 0
  thus ?case
    by simp
next
  case (Suc k)
  have "l ! i \<succ> (l ! (i + 1))"
    using Suc(3) Suc(4) Suc(5)
    unfolding rel_chain_def
    by auto
  hence "\<triangle> (\<T> (l ! (i + 1)))"
    by (rule succ_inv)

  show ?case
  proof (cases "x \<in> rvars (\<T> (l ! (i + 1)))")
    case True
    hence "j \<noteq> i + 1"
      using Suc(7) `\<triangle> (\<T> (l ! (i + 1)))`
      by (auto simp add: normalized_tableau_def)
    have "k = j - Suc i"
      using Suc(2)
      by simp
    then obtain k where "k \<ge> i + 1" "k < j" "swap_rl l k x"
      using `x \<in> rvars (\<T> (l ! (i + 1)))` `j \<noteq> i + 1`
      using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5) Suc(6) Suc(7)
      by auto
    thus ?thesis
      by (rule_tac x="k" in exI) simp
  next
    case False
    hence "x \<in> lvars (\<T> (l ! (i + 1)))"
      using Suc(6)
      using `l ! i \<succ> (l ! (i + 1))` succ_vars_id
      by auto
    thus ?thesis
      using Suc(4) Suc(5) Suc(6)
      by force
  qed
qed

lemma succ_chain_swap_lr_exists:
  assumes "succ_chain l" "i < j" "j < length l"
  "x \<in> lvars (\<T> (l ! i))" "x \<in> rvars (\<T> (l ! j))"
  shows "\<exists> k. i \<le> k \<and> k < j \<and> swap_lr l k x"
using assms
proof (induct "j - i" arbitrary: i)
  case 0
  thus ?case
    by simp
next
  case (Suc k)
  have "l ! i \<succ> (l ! (i + 1))"
    using Suc(3) Suc(4) Suc(5)
    unfolding rel_chain_def
    by auto
  hence "\<triangle> (\<T> (l ! (i + 1)))"
    by (rule succ_inv)

  show ?case
  proof (cases "x \<in> lvars (\<T> (l ! (i + 1)))")
    case True
    hence "j \<noteq> i + 1"
      using Suc(7) `\<triangle> (\<T> (l ! (i + 1)))`
      by (auto simp add: normalized_tableau_def)
    have "k = j - Suc i"
      using Suc(2)
      by simp
    then obtain k where "k \<ge> i + 1" "k < j" "swap_lr l k x"
      using `x \<in> lvars (\<T> (l ! (i + 1)))` `j \<noteq> i + 1`
      using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5) Suc(6) Suc(7)
      by auto
    thus ?thesis
      by (rule_tac x="k" in exI) simp
  next
    case False
    hence "x \<in> rvars (\<T> (l ! (i + 1)))"
      using Suc(6)
      using `l ! i \<succ> (l ! (i + 1))` succ_vars_id
      by auto
    thus ?thesis
      using Suc(4) Suc(5) Suc(6)
      by force
  qed
qed

(* -------------------------------------------------------------------------- *)

lemma finite_tableaus_aux:
  shows "finite {t. lvars t = L \<and> rvars t = V - L \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}" (is "finite (?Al L)")
proof (cases "?Al L = {}")
  case True
  show ?thesis
    by (subst True) simp
next
  case False
  hence "\<exists> t. t \<in> ?Al L"
    by auto
  let ?t = "SOME t. t \<in> ?Al L"
  have "?t \<in> ?Al L"
    using `\<exists> t. t \<in> ?Al L`
    by (rule someI_ex)
  have "?Al L \<subseteq> {t. t <~~> ?t}"
  proof
    fix x
    assume "x \<in> ?Al L"
    have "x <~~> ?t"
      apply (rule tableau_perm)
      using `?t \<in> ?Al L` `x \<in> ?Al L`
      by auto
    thus "x \<in> {t. t <~~> ?t}"
      by simp
  qed
  moreover
  have "finite {t. t <~~> ?t}"
    by (rule perm_finite)
  ultimately
  show ?thesis
    by (rule finite_subset)
qed

lemma finite_tableaus:
  assumes "finite V"
  shows "finite {t. tvars t = V \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}" (is "finite ?A")
proof-
  let ?Al = "\<lambda> L. {t. lvars t = L \<and> rvars t = V - L \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}"
  have "?A = \<Union> (?Al ` {L. L \<subseteq> V})"
    by (auto simp add: normalized_tableau_def)
  thus ?thesis
    using `finite V`
    using finite_tableaus_aux
    by auto
qed

lemma finite_accessible_tableaus:
  shows "finite (\<T> ` {s'. s \<succ>\<^sup>* s'})"
proof-
  have "{s'. s \<succ>\<^sup>* s'} = {s'. s \<succ>\<^sup>+ s'} \<union> {s}"
    by (auto simp add: rtrancl_eq_or_trancl)
  moreover
  have "finite (\<T> ` {s'. s \<succ>\<^sup>+ s'})" (is "finite ?A")
  proof-
    let ?T = "{t. tvars t = tvars (\<T> s) \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t(\<T> s))}"
    have "?A \<subseteq> ?T"
    proof
      fix t
      assume "t \<in> ?A"
      then obtain s' where "s \<succ>\<^sup>+ s'" "t = \<T> s'"
        by auto
      then obtain l where *: "l \<noteq> []" "1 < length l" "hd l = s" "last l = s'" "succ_chain l"
        using trancl_rel_chain[of s s' succ_rel]
        by auto
      show "t \<in> ?T"
      proof-
        have "tvars (\<T> s') = tvars (\<T> s)"
          using succ_chain_vars_id[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by simp
        moreover
        have "\<triangle> (\<T> s')"
          using `s \<succ>\<^sup>+ s'`
          using succ_inv(1)[of _ s']
          by (auto dest: tranclD2)
        moreover
        have "\<forall>v::'a valuation. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t \<T> s"
          using succ_chain_tableau_equiv[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        ultimately
        show ?thesis
          using `t = \<T> s'`
          by simp
      qed
    qed
    moreover
    have "finite (tvars (\<T> s))"
      by (auto simp add: lvars_def rvars_def finite_vars)
    ultimately
    show ?thesis
      using finite_tableaus[of "tvars (\<T> s)" "\<T> s"]
      by (auto simp add: finite_subset)
  qed
  ultimately
  show ?thesis
    by simp
qed

abbreviation check_valuation  where
 "check_valuation (v::'a valuation) v0 bl0 bu0 t0 V \<equiv> 
     \<exists> t. tvars t = V \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0) \<and> v \<Turnstile>\<^sub>t t \<and> 
     (\<forall> x \<in> rvars t. v x = v0 x \<or> v x = bl0 x \<or> v x = bu0 x) \<and> 
     (\<forall> x. x \<notin> V \<longrightarrow> v x = v0 x)"

lemma finite_valuations:
  assumes "finite V"
  shows "finite {v::'a valuation. check_valuation v v0 bl0 bu0 t0 V}" (is "finite ?A")
proof-
  let ?Al = "\<lambda> L. {t. lvars t = L \<and> rvars t = V - L \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}"
  let ?Vt = "\<lambda> t. {v::'a valuation. v \<Turnstile>\<^sub>t t \<and> (\<forall> x \<in> rvars t. v x = v0 x \<or> v x = bl0 x \<or> v x = bu0 x) \<and> (\<forall> x. x \<notin> V \<longrightarrow> v x = v0 x)}"

  have "finite {L. L \<subseteq> V}"
    using `finite V` 
    by auto
  have "\<forall> L. L \<subseteq> V \<longrightarrow> finite (?Al L)"
    using finite_tableaus_aux
    by auto
  have "\<forall> L t. L \<subseteq> V \<and> t \<in> ?Al L \<longrightarrow> finite (?Vt  t)"
  proof (safe)
    fix L t
    assume "lvars t \<subseteq> V" "rvars t = V - lvars t" "\<triangle> t" "\<forall>v. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0"
    hence "rvars t \<union> lvars t = V"
      by auto

    let ?f = "\<lambda> v x. if x \<in> rvars t then v x else 0"

    have "inj_on ?f (?Vt t)"
      unfolding inj_on_def
    proof (safe, rule ext)
      fix v1 v2 x
      assume "(\<lambda>x. if x \<in> rvars t then v1 x else (0 :: 'a)) =
              (\<lambda>x. if x \<in> rvars t then v2 x else (0 :: 'a))" (is "?f1 = ?f2")
      have "\<forall>x\<in>rvars t. v1 x = v2 x"
      proof
        fix x 
        assume "x \<in> rvars t"
        thus "v1 x = v2 x"
          using `?f1 = ?f2` fun_cong[of ?f1 ?f2 x]
          by auto
      qed
      assume *: "v1 \<Turnstile>\<^sub>t t" "v2 \<Turnstile>\<^sub>t t"
                "\<forall>x. x \<notin> V \<longrightarrow> v1 x = v0 x" "\<forall>x. x \<notin> V \<longrightarrow> v2 x = v0 x"
      show "v1 x = v2 x"
      proof (cases "x \<in> lvars t")
        case False
        thus ?thesis
          using * `\<forall>x\<in>rvars t. v1 x = v2 x` `rvars t \<union> lvars t = V`
          by auto
      next
        case True
        let ?eq = "eq_for_lvar t x"
        have "?eq \<in> set t \<and> lhs ?eq = x"
          using eq_for_lvar `x \<in> lvars t`
          by simp
        hence "v1 x = rhs ?eq \<lbrace> v1 \<rbrace>" "v2 x = rhs ?eq \<lbrace> v2 \<rbrace>"
          using `v1 \<Turnstile>\<^sub>t t` `v2 \<Turnstile>\<^sub>t t`
          unfolding satisfies_tableau_def satisfies_eq_def
          by auto
        moreover
        have "rhs ?eq \<lbrace> v1 \<rbrace> = rhs ?eq \<lbrace> v2 \<rbrace>"
          apply (rule valuate_depend)
          using `\<forall>x\<in>rvars t. v1 x = v2 x` `?eq \<in> set t \<and> lhs ?eq = x`
          unfolding rvars_def
          by auto
        ultimately
        show ?thesis
          by simp
      qed
    qed

    let ?R = "{v. \<forall> x. if x \<in> rvars t then v x = v0 x \<or> v x = bl0 x \<or> v x = bu0 x else v x = 0 }"
    have "?f ` (?Vt t) \<subseteq> ?R"
      by auto
    moreover
    have "finite ?R"
    proof-
      have "finite (rvars t)"
        using `finite V` `rvars t \<union> lvars t = V`
        using  finite_subset[of "rvars t" V]
        by auto
      moreover
      let ?R' = "{v. \<forall> x. if x \<in> rvars t then v x \<in> {v0 x, bl0 x, bu0 x} else v x = 0}"
      have "?R = ?R'"
        by auto
      ultimately
      show ?thesis
        using finite_fun_args[of "rvars t" "\<lambda> x. {v0 x,  bl0 x, bu0 x}" "\<lambda> x. 0"]
        by auto
    qed
    ultimately
    have "finite (?f ` (?Vt t))"
      by (simp add: finite_subset)
    thus "finite (?Vt t)"
      using `inj_on ?f (?Vt t)`
      by (auto dest: finite_imageD)
  qed

  have "?A = \<Union> \<Union> ((op ` ?Vt) ` (?Al ` {L. L \<subseteq> V}))" (is "?A = ?A'")
    by (auto simp add: normalized_tableau_def)
  moreover
  have "finite ?A'"
  proof (rule finite_Union)
    show "finite (\<Union> ((op ` ?Vt) ` (?Al ` {L. L \<subseteq> V})))"
      using `finite {L. L \<subseteq> V}` `\<forall> L. L \<subseteq> V \<longrightarrow> finite (?Al L)`
      by auto
  next
    fix M
    assume "M \<in> \<Union> ((op ` ?Vt) ` (?Al ` {L. L \<subseteq> V}))"
    then obtain L t where "L \<subseteq> V" "t \<in> ?Al L" "M = ?Vt t"
      by blast
    thus "finite M"
      using `\<forall> L t. L \<subseteq> V \<and> t \<in> ?Al L \<longrightarrow> finite (?Vt  t)`
      by blast
  qed
  ultimately
  show ?thesis
    by simp
qed


lemma finite_accessible_valuations:
  shows "finite (\<V> ` {s'. s \<succ>\<^sup>* s'})"
proof-
  have "{s'. s \<succ>\<^sup>* s'} = {s'. s \<succ>\<^sup>+ s'} \<union> {s}"
    by (auto simp add: rtrancl_eq_or_trancl)
  moreover
  have "finite (\<V> ` {s'. s \<succ>\<^sup>+ s'})" (is "finite ?A")
  proof-
    let ?P = "\<lambda> v. check_valuation v (\<langle>\<V> s\<rangle>) (\<lambda> x. the (\<B>\<^sub>l s x)) (\<lambda> x. the (\<B>\<^sub>u s x)) (\<T> s) (tvars (\<T> s))"
    let ?P' = "\<lambda> v::(var, 'a) mapping.
         \<exists> t. tvars t = tvars (\<T> s) \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> s) \<and> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<and> 
    (\<forall> x \<in> rvars t. \<langle>v\<rangle> x = \<langle>\<V> s\<rangle> x \<or> 
                       \<langle>v\<rangle> x = the (\<B>\<^sub>l s x) \<or> 
                       \<langle>v\<rangle> x = the (\<B>\<^sub>u s x)) \<and> 
    (\<forall> x. x \<notin> tvars (\<T> s) \<longrightarrow> look v x = look (\<V> s) x) \<and> 
    (\<forall> x. x \<in> tvars (\<T> s) \<longrightarrow> look v x \<noteq> None)"

    have "finite (tvars (\<T> s))"
      by (auto simp add: lvars_def rvars_def finite_vars)
    hence "finite {v. ?P v}"
      using finite_valuations[of "tvars (\<T> s)" "\<T> s" "\<langle>\<V> s\<rangle>" "\<lambda> x. the (\<B>\<^sub>l s x)" "\<lambda> x. the (\<B>\<^sub>u s x)"]
      by auto
    moreover
    have "map2fun ` {v. ?P' v} \<subseteq> {v. ?P v}"
      by (auto simp add: map2fun_def) (rule_tac x=t in exI, auto)
    ultimately
    have "finite (map2fun ` {v. ?P' v})"
      by (auto simp add: finite_subset)
    moreover
    have "inj_on map2fun {v. ?P' v}"
      unfolding inj_on_def
    proof (safe)
      fix x y
      assume "\<langle>x\<rangle> = \<langle>y\<rangle>" and *:
        "\<forall>x. x \<notin> Simplex_Export.tvars (\<T> s) \<longrightarrow> look y x = look (\<V> s) x"
        "\<forall>xa. xa \<notin> Simplex_Export.tvars (\<T> s) \<longrightarrow> look x xa = look (\<V> s) xa"
        "\<forall>x. x \<in> Simplex_Export.tvars (\<T> s) \<longrightarrow> look y x \<noteq> None"
        "\<forall>xa. xa \<in> Simplex_Export.tvars (\<T> s) \<longrightarrow> look x xa \<noteq> None"
      show "x = y"
      proof (rule mapping_eqI)
        fix k
        have "\<langle>x\<rangle> k = \<langle>y\<rangle> k"
          using `\<langle>x\<rangle> = \<langle>y\<rangle>`
          by simp
        thus "look x k = look y k"
          using *
          by  (cases "k \<in> tvars (\<T> s)") (auto simp add: map2fun_def split: option.split)
      qed
    qed
    ultimately
    have "finite {v. ?P' v}"
      by (rule finite_imageD)
    moreover
    have "?A \<subseteq> {v. ?P' v}"
    proof (safe)
      fix s'
      assume "s \<succ>\<^sup>+ s'"
      then obtain l where *: "l \<noteq> []" "1 < length l" "hd l = s" "last l = s'" "succ_chain l"
        using trancl_rel_chain[of s s' succ_rel]
        by auto
      show "?P' (\<V> s')"
      proof-
        have "\<nabla> s" "\<triangle> (\<T> s)" "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
          using `s \<succ>\<^sup>+ s'`
          using tranclD[of s s' succ_rel]
          by (auto simp add: curr_val_satisfies_no_lhs_def)
        have "tvars (\<T> s') = tvars (\<T> s)"
          using succ_chain_vars_id[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by simp
        moreover
        have "\<triangle>(\<T> s')"
          using `s \<succ>\<^sup>+ s'`
          using succ_inv(1)[of _ s']
          by (auto dest: tranclD2)
        moreover
        have "\<forall>v::'a valuation. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t \<T> s"
          using succ_chain_tableau_equiv[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        moreover
        have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'"
          using succ_chain_valuation_satisfies[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l] `\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s`
          by simp
        moreover
        have "\<forall>x\<in>rvars (\<T> s'). \<langle>\<V> s'\<rangle> x = \<langle>\<V> s\<rangle> x \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>l s x) \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>u s x)"
          using succ_chain_rvar_valuation[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        moreover
        have "\<forall>x. x \<notin> tvars (\<T> s) \<longrightarrow> look (\<V> s') x = look (\<V> s) x"
          using succ_chain_no_vars_valuation[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        moreover
        have "\<forall>x. x \<in> Simplex_Export.tvars (\<T> s') \<longrightarrow> look (\<V> s') x \<noteq> None"
          using succ_chain_tableau_valuated[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          using `tvars (\<T> s') = tvars (\<T> s)` `\<nabla> s`
          by (auto simp add: tableau_valuated_def)
        ultimately
        show ?thesis
          by (rule_tac x="\<T> s'" in exI) auto
      qed
    qed
    ultimately
    show ?thesis
      by (auto simp add: finite_subset)
  qed
  ultimately
  show ?thesis
    by simp
qed

lemma accessible_valuations:
  shows "\<B> ` {s'. s \<succ>\<^sup>* s'} = {\<B> s}"
proof (auto)
  fix s'
  assume "s \<succ>\<^sup>* s'"
  have "\<B> s' = \<B> s"
  proof (cases "s = s'")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence "s \<succ>\<^sup>+ s'"
      using `s \<succ>\<^sup>* s'`
      by (auto dest: rtranclD)
    then obtain l where *: "l \<noteq> []" "1 < length l" "hd l = s" "last l = s'" "succ_chain l"
      using trancl_rel_chain[of s s' succ_rel]
      by auto
    thus ?thesis
      using succ_chain_bounds_id[of l 0 "length l - 1"]
      using hd_conv_nth[of l] last_conv_nth[of l]
      by auto
  qed
  thus "\<B>\<^sub>l s' = \<B>\<^sub>l s" "\<B>\<^sub>u s' = \<B>\<^sub>u s"
    by auto
qed

lemma finite_accessible_states:
  shows "finite {s'. s \<succ>\<^sup>* s'}" (is "finite ?A")
proof-
  let ?V = "\<V> ` ?A"
  let ?T = "\<T> ` ?A"
  let ?P = "?V \<times> ?T \<times> {\<B> s} \<times> {True, False}"
  have "finite ?P"
    using finite_accessible_valuations finite_accessible_tableaus
    by auto
  moreover
  let ?f = "\<lambda> s. (\<V> s, \<T> s, \<B> s, \<U> s)"
  have "?f ` ?A \<subseteq> ?P"
    using accessible_valuations
    by auto
  moreover
  have "inj_on ?f ?A"
    unfolding inj_on_def
    by auto
  ultimately
  show ?thesis
    using finite_imageD [of ?f ?A]
    using finite_subset
    by auto
qed

(* -------------------------------------------------------------------------- *)
lemma acyclic_suc_rel: "acyclic succ_rel"
proof (rule acyclicI, rule allI)
  fix s
  show "(s, s) \<notin> succ_rel\<^sup>+"
  proof
    assume "s \<succ>\<^sup>+ s"
    then obtain l where
      "l \<noteq> []" "length l > 1" "hd l = s" "last l = s" "succ_chain l"
      using trancl_rel_chain[of s s succ_rel]
      by auto

    have "l ! 0 = s"
      using `l \<noteq> []` `hd l = s`
      by (simp add: hd_conv_nth)
    hence "s \<succ> (l ! 1)"
      using `succ_chain l`
      unfolding rel_chain_def
      using `length l > 1`
      by auto
    hence "\<triangle> (\<T> s)"
      by simp

    let ?enter_rvars = 
      "{x. \<exists> sl. swap_lr l sl x}"

    have "finite ?enter_rvars"
    proof-
      let ?all_vars = "(\<Union> set (map (\<lambda> t. lvars t \<union> rvars t) (map \<T> l)))"
      have "finite ?all_vars"
        by (auto simp add: lvars_def rvars_def finite_vars)
      moreover
      have "?enter_rvars \<subseteq> ?all_vars"
        by force
      ultimately
      show ?thesis
        by (simp add: finite_subset)
    qed

    let ?xr = "Max ?enter_rvars"
    have "?xr \<in> ?enter_rvars"
    proof (rule Max_in)
      show "?enter_rvars \<noteq> {}"
      proof-
        from `s \<succ> (l ! 1)`
        obtain x\<^sub>i x\<^sub>j :: var where
          "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<in> rvars (\<T> (l ! 1))"
          by (rule succ_vars) auto
        hence "x\<^sub>i \<in> ?enter_rvars"
          using `hd l = s` `l \<noteq> []` `length l > 1`
          by (auto simp add: hd_conv_nth)
        thus ?thesis
          by auto
      qed
    next
      show "finite ?enter_rvars"
        using `finite ?enter_rvars`
        .
    qed
    then obtain xr sl where 
      "xr = ?xr" "swap_lr l sl xr"
      by auto
    hence "sl + 1 < length l"
      by simp

    have "(l ! sl) \<succ> (l ! (sl + 1))"
      using `sl + 1 < length l` `succ_chain l`
      unfolding rel_chain_def
      by auto


    have "length l > 2"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with `length l > 1`
      have "length l = 2"
        by auto
      hence "last l = l ! 1"
        by (cases l) (auto simp add: last_conv_nth nth_Cons split: nat.split)
      hence "xr \<in> lvars (\<T> s)" "xr \<in> rvars (\<T> s)"
        using `length l = 2`
        using `swap_lr l sl xr`
        using `hd l = s` `last l = s` `l \<noteq> []`
        by (auto simp add: hd_conv_nth)
      thus False
        using `\<triangle> (\<T> s)`
        unfolding normalized_tableau_def
        by auto
    qed

    obtain l' where
      "hd l' = l ! (sl + 1)" "last l' = l ! sl" "length l' = length l - 1"  "succ_chain l'" and
      l'_l:   "\<forall> i. i + 1 < length l' \<longrightarrow> 
     (\<exists> j. j + 1 < length l \<and> l' ! i = l ! j \<and> l' ! (i + 1) = l ! (j + 1))"
      using `length l > 2` `sl + 1 < length l` `hd l = s` `last l = s` `succ_chain l`
      using reorder_cyclic_list[of l s sl]
      by blast

    hence "xr \<in> rvars (\<T> (hd l'))"  "xr \<in> lvars (\<T> (last l'))" "length l' > 1" "l' \<noteq> []"
      using `swap_lr l sl xr` `length l > 2`
      by auto

    hence "\<exists> sp. swap_rl l' sp xr"
      using `succ_chain l'`
      using succ_chain_swap_rl_exists[of l' 0 "length l' - 1" xr]
      by (auto simp add: hd_conv_nth last_conv_nth)
    hence "\<exists> sp. swap_rl l' sp xr \<and> (\<forall> sp'. sp' < sp \<longrightarrow> \<not> swap_rl l' sp' xr)"
      by (rule min_element)
    then obtain sp where
      "swap_rl l' sp xr" "\<forall> sp'. sp' < sp \<longrightarrow> \<not> swap_rl l' sp' xr"
      by blast
    hence "sp + 1 < length l'"
      by simp
    
    have "\<langle>\<V> (l' ! 0)\<rangle> xr = \<langle>\<V> (l' ! sp)\<rangle> xr"
    proof-
      have "always_r l' 0 sp xr"
        using `xr \<in> rvars (\<T> (hd l'))` `sp + 1 < length l'`
          `\<forall> sp'. sp' < sp \<longrightarrow> \<not> swap_rl l' sp' xr`
      proof (induct sp)
        case 0
        hence "l' \<noteq> []"
          by auto
        thus ?case
          using 0(1)
          by (auto simp add: hd_conv_nth)
      next
        case (Suc sp')
        show ?case
        proof (safe)
          fix k
          assume "k \<le> Suc sp'"
          show "xr \<in> rvars (\<T> (l' ! k))"
          proof (cases "k = sp' + 1")
            case False
            thus ?thesis
              using Suc `k \<le> Suc sp'`
              by auto
          next
            case True
            hence "xr \<in> rvars (\<T> (l' ! (k - 1)))"
              using Suc
              by auto
            moreover
            hence "xr \<notin> lvars (\<T> (l' ! k))"
              using True Suc(3) Suc(4)
              by auto
            moreover
            have "(l' ! (k - 1)) \<succ> (l' ! k)" 
              using `succ_chain l'`
              using Suc(3) True
              by (simp add: rel_chain_def)
            ultimately
            show ?thesis
              using succ_vars_id[of "l' ! (k - 1)" "l' ! k"]
              by auto
          qed
        qed
      qed
      thus ?thesis
        using `sp + 1 < length l'`
        using `succ_chain l'`
        using succ_chain_always_r_valuation_id
        by simp
    qed
    
    have "(l' ! sp) \<succ> (l' ! (sp+1))"
      using `sp + 1 < length l'` `succ_chain l'`
      unfolding rel_chain_def
      by simp
    then obtain xs xr' :: var where 
      "xs \<in> lvars (\<T> (l' ! sp))"
      "xr \<in> rvars (\<T> (l' ! sp))"
      "swap_lr l' sp xs"
      apply (rule succ_vars)
      using `swap_rl l' sp xr` `sp + 1 < length l'`
      by auto
    hence "xs \<noteq> xr"
      using `(l' ! sp) \<succ> (l' ! (sp+1))`
      by (auto simp add: normalized_tableau_def)

    obtain sp' where 
      "l' ! sp = l ! sp'" "l' ! (sp + 1) = l ! (sp' + 1)"
      "sp' + 1 < length l"
      using `sp + 1 < length l'` l'_l
      by auto

    have "xs \<in> ?enter_rvars"
      using `swap_lr l' sp xs` l'_l
      by force
    
    have "xs < xr"
    proof-
      have "xs \<le> ?xr"
        using `finite ?enter_rvars` `xs \<in> ?enter_rvars`
        by (rule Max_ge)
      thus ?thesis
        using `xr = ?xr` `xs \<noteq> xr`
        by simp
    qed

    let ?sl = "l ! sl"
    let ?sp = "l' ! sp"
    let ?eq = "eq_for_lvar (\<T> ?sp) xs"
    let ?bl = "\<V> ?sl"
    let ?bp = "\<V> ?sp"

    have "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sl" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sp"
      using `l ! sl \<succ> (l ! (sl + 1))`
      using `l' ! sp \<succ> (l' ! (sp+ 1))`
      by simp_all

    have "\<B> ?sp = \<B> ?sl"
    proof-
      have "\<B> (l' ! sp) = \<B> (l' ! (length l' - 1))"
        using `sp + 1 < length l'` `succ_chain l'`
        using succ_chain_bounds_id
        by auto
      hence "\<B> (last l') = \<B> (l' ! sp)"
        using `l' \<noteq> []` 
        by (simp add: last_conv_nth)
      thus ?thesis
        using `last l' = l ! sl`
        by simp
    qed

    have diff_satified: "\<langle>?bl\<rangle> xs - \<langle>?bp\<rangle> xs = ((rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>) - ((rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>)" 
    proof-
      have "\<langle>?bp\<rangle> \<Turnstile>\<^sub>e ?eq"
        using `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sp`
        using eq_for_lvar[of xs "\<T> ?sp"]
        using `xs \<in> lvars (\<T> (l' ! sp))`
        unfolding curr_val_satisfies_no_lhs_def satisfies_tableau_def
        by auto
      moreover
      have "\<langle>?bl\<rangle> \<Turnstile>\<^sub>e ?eq"
      proof-
        have "\<langle>\<V> (l ! sl)\<rangle> \<Turnstile>\<^sub>t \<T> (l' ! sp)"
          using `l' ! sp = l ! sp'` `sp' + 1 < length l` `sl + 1 < length l`
          using `succ_chain l`
          using succ_chain_tableau_equiv[of l sl sp']
          using `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sl`
          unfolding curr_val_satisfies_no_lhs_def
          by simp
        thus ?thesis
          unfolding satisfies_tableau_def
          using eq_for_lvar
          using `xs \<in> lvars (\<T> (l' ! sp))`
          by simp
      qed
      moreover
      have "lhs ?eq = xs"
        using `xs \<in> lvars (\<T> (l' ! sp))` 
        using eq_for_lvar
        by simp
      ultimately
      show ?thesis
        unfolding satisfies_eq_def 
        by auto
    qed

    have "\<not> in_bounds xr \<langle>?bl\<rangle> (\<B> ?sl)"
      using `l ! sl \<succ> (l ! (sl + 1))`  `swap_lr l sl xr`
      using succ_min_lvar_not_in_bounds(1)[of ?sl "l ! (sl + 1)" xr]
      by simp

    have "\<forall> x. x < xr \<longrightarrow> in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)"
    proof (safe)
      fix x
      assume "x < xr"
      show "in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)"
      proof (cases "x \<in> lvars (\<T> ?sl)")
        case True
        thus ?thesis
          using succ_min_lvar_not_in_bounds(2)[of ?sl "l ! (sl + 1)" xr]
          using `l ! sl \<succ> (l ! (sl + 1))`  `swap_lr l sl xr` `x < xr`
          by simp
      next
        case False
        thus ?thesis
          using `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sl`
          unfolding curr_val_satisfies_no_lhs_def
          by (simp add: satisfies_bounds_set.simps)
      qed
    qed

    hence "in_bounds xs \<langle>?bl\<rangle> (\<B> ?sl)"
      using `xs < xr`
      by simp

    have "\<not> in_bounds xs \<langle>?bp\<rangle> (\<B> ?sp)"
      using `l' ! sp \<succ> (l' ! (sp + 1))`  `swap_lr l' sp xs`
      using succ_min_lvar_not_in_bounds(1)[of ?sp "l' ! (sp + 1)" xs]
      by simp

    have "\<forall> x \<in> rvars_eq ?eq. x > xr \<longrightarrow> \<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x"
    proof (safe)
      fix x
      assume "x \<in> rvars_eq ?eq" "x > xr"
      hence "always_r l' 0 (length l' - 1) x"
      proof (safe)
        fix k
        assume "x \<in> rvars_eq ?eq" "x > xr" "0 \<le> k" "k \<le> length l' - 1"
        obtain k' where "l ! k' = l' ! k" "k' < length l"
          using l'_l `k \<le> length l' - 1` `length l' > 1`
          apply (cases "k > 0")
          apply (erule_tac x="k - 1" in allE)
          apply (drule mp)
          by auto

        let ?eq' = "eq_for_lvar (\<T> (l ! sp')) xs"

        have "\<forall> x \<in> rvars_eq ?eq'. x > xr \<longrightarrow> always_r l 0 (length l - 1) x"
        proof (safe)
          fix x k
          assume "x \<in> rvars_eq ?eq'" "xr < x" "0 \<le> k" "k \<le> length l - 1"
          hence "x \<in> rvars (\<T> (l ! sp'))"
            using eq_for_lvar[of xs "\<T> (l ! sp')"]
            using `swap_lr l' sp xs` `l' ! sp = l ! sp'`
            by (auto simp add: rvars_def)
          have *: "\<forall> i. i < sp' \<longrightarrow> x \<in> rvars (\<T> (l ! i))"
          proof (safe, rule ccontr)
            fix i
            assume "i < sp'" "x \<notin> rvars (\<T> (l ! i))"
            hence "x \<in> lvars (\<T> (l ! i))"
              using `x \<in> rvars (\<T> (l ! sp'))`
              using `sp' + 1 < length l`
              using `succ_chain l`
              using succ_chain_vars_id[of l i sp']
              by auto
            obtain i' where "swap_lr l i' x"
              using `x \<in> lvars (\<T> (l ! i))`
              using `x \<in> rvars (\<T> (l ! sp'))`
              using `i < sp'` `sp' + 1 < length l`
              using `succ_chain l`
              using succ_chain_swap_lr_exists[of l i sp' x]
              by auto
            hence "x \<in> ?enter_rvars"
              by auto
            hence "x \<le> ?xr"
              using `finite ?enter_rvars`
              using Max_ge[of ?enter_rvars x]
              by simp
            thus False
              using `x > xr`
              using `xr = ?xr`
              by simp
          qed

          hence "x \<in> rvars (\<T> (last l))"
            using `hd l = s` `last l = s` `l \<noteq> []`
            using `x \<in> rvars (\<T> (l ! sp'))`
            by (auto simp add: hd_conv_nth)

          show "x \<in> rvars (\<T> (l ! k))"
          proof (cases "k = length l - 1")
            case True
            thus ?thesis
              using `x \<in> rvars (\<T> (last l))`
              using `l \<noteq> []`
              by (simp add: last_conv_nth)
          next
            case False
            hence "k < length l - 1"
              using `k \<le> length l - 1`
              by simp
            hence "k < length l"
              using `length l > 1`
              by auto
            show ?thesis
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "x \<in> lvars (\<T> (l ! k))"
                using `x \<in> rvars (\<T> (l ! sp'))`
                using `sp' + 1 < length l` `k < length l`
                using succ_chain_vars_id[of l k sp']
                using `succ_chain l` `l \<noteq> []`
                by auto
              obtain i' where "swap_lr l i' x"
                using `succ_chain l`
                using `x \<in> lvars (\<T> (l ! k))`
                using `x \<in> rvars (\<T> (last l))`
                using `k < length l - 1` `l \<noteq> []`
                using succ_chain_swap_lr_exists[of l k "length l - 1" x]
                by (auto simp add: last_conv_nth)
              hence "x \<in> ?enter_rvars"
                by auto
              hence "x \<le> ?xr"
                using `finite ?enter_rvars`
                using Max_ge[of ?enter_rvars x]
                by simp
              thus False
                using `x > xr`
                using `xr = ?xr`
                by simp
            qed
          qed
        qed
        hence "x \<in> rvars (\<T> (l ! k'))"
          using `x \<in> rvars_eq ?eq` `x > xr` `k' < length l`
          using `l' ! sp = l ! sp'`
          by simp

        thus "x \<in> rvars (\<T> (l' ! k))"
          using `l ! k' = l' ! k`
          by simp
      qed
      hence "\<langle>?bp\<rangle> x = \<langle>\<V> (l' ! (length l' - 1))\<rangle> x"
        using `succ_chain l'` `sp + 1 < length l'`
        by (auto intro!: succ_chain_always_r_valuation_id[rule_format])
      hence "\<langle>?bp\<rangle> x = \<langle>\<V> (last l')\<rangle> x"
        using `l' \<noteq> []`
        by (simp add: last_conv_nth)
      thus "\<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x"
        using `last l' = l ! sl`
        by simp
    qed

    have "\<langle>?bp\<rangle> xr = \<langle>\<V> (l ! (sl + 1))\<rangle> xr"
      using `\<langle>\<V> (l' ! 0)\<rangle> xr = \<langle>\<V> (l' ! sp)\<rangle> xr`
      using `hd l' = l ! (sl + 1)` `l' \<noteq> []`
      by (simp add: hd_conv_nth)

    {
      fix dir1 dir2 :: "'a Direction"
      assume dir1: "dir1 = (if \<langle>?bl\<rangle> xr <\<^sub>l\<^sub>b \<B>\<^sub>l ?sl xr then Positive else Negative)"
      hence "\<lhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)"
        using `\<not> in_bounds xr \<langle>?bl\<rangle> (\<B> ?sl)`
        using neg_bounds_compare(7) neg_bounds_compare(3)
        by (auto simp add: bound_compare''_defs)
      hence "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)"
        using bounds_compare_contradictory(7) bounds_compare_contradictory(3) neg_bounds_compare(6) dir1
        unfolding bound_compare''_defs
        by auto force
      have "LB dir1 ?sl xr \<noteq> None"
        using `\<lhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)`
        by (cases "LB dir1 ?sl xr")  (auto simp add: bound_compare_defs)

      assume dir2: "dir2 = (if \<langle>?bp\<rangle> xs <\<^sub>l\<^sub>b \<B>\<^sub>l ?sp xs then Positive else Negative)"
      hence "\<lhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)"
        using `\<not> in_bounds xs \<langle>?bp\<rangle> (\<B> ?sp)`
        using neg_bounds_compare(2) neg_bounds_compare(6)
        by (auto simp add: bound_compare''_defs)
      hence "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)"
        using bounds_compare_contradictory(3) bounds_compare_contradictory(7) neg_bounds_compare(6) dir2
        unfolding bound_compare''_defs
        by auto force
      hence "\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> \<not> reasable_var dir2 x ?eq ?sp"
        using succ_min_rvar[of ?sp "l' ! (sp + 1)" xs xr ?eq]
        using `l' ! sp \<succ> (l' ! (sp + 1))`
        using `swap_lr l' sp xs` `swap_rl l' sp xr` dir2
        unfolding bound_compare''_defs
        by auto

      have "LB dir2 ?sp xs \<noteq> None"
        using `\<lhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)`
        by (cases "LB dir2 ?sp xs")  (auto simp add: bound_compare_defs)

      have *: "\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> 
        ((coeff (rhs ?eq) x > 0 \<longrightarrow> \<unrhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (UB dir2 ?sp x)) \<and> 
         (coeff (rhs ?eq) x < 0 \<longrightarrow> \<unlhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (LB dir2 ?sp x)))"
      proof (safe)
        fix x
        assume "x \<in> rvars_eq ?eq" "x < xr" "coeff (rhs ?eq) x > 0"
        hence "\<not> \<lhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (UB dir2 ?sp x)"
          using `\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> \<not> reasable_var dir2 x ?eq ?sp`
          by simp
        thus "\<unrhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (UB dir2 ?sp x)"
          using dir2 neg_bounds_compare(4) neg_bounds_compare(8)
          unfolding bound_compare''_defs
          by force
      next
        fix x
        assume "x \<in> rvars_eq ?eq" "x < xr" "coeff (rhs ?eq) x < 0"
        hence "\<not> \<rhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (LB dir2 ?sp x)"
          using `\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> \<not> reasable_var dir2 x ?eq ?sp`
          by simp
        thus "\<unlhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (LB dir2 ?sp x)"
          using dir2 neg_bounds_compare(4) neg_bounds_compare(8) dir2
          unfolding bound_compare''_defs
          by force
      qed

      have "(lt dir2) (\<langle>?bp\<rangle> xs) (\<langle>?bl\<rangle> xs)"
        using `\<lhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)`
        using `\<B> ?sp = \<B> ?sl` dir2
        using `in_bounds xs \<langle>?bl\<rangle> (\<B> ?sl)`
        by (auto simp add: bound_compare''_defs)
      hence "(lt dir2) 0 (\<langle>?bl\<rangle> xs - \<langle>?bp\<rangle> xs)"
        using dir2
        by (auto simp add: minus_gt[THEN sym] minus_lt[THEN sym])

      moreover

      have "le (lt dir2) ((rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace> - (rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>) 0"
      proof-
        have "\<forall> x \<in> rvars_eq ?eq. (0 < coeff (rhs ?eq) x \<longrightarrow> le (lt dir2) 0 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x)) \<and> 
                    (coeff (rhs ?eq) x < 0 \<longrightarrow> le (lt dir2) (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x) 0)"
        proof
          fix x
          assume "x \<in> rvars_eq ?eq"
          show "(0 < coeff (rhs ?eq) x \<longrightarrow> le (lt dir2) 0 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x)) \<and> 
                (coeff (rhs ?eq) x < 0 \<longrightarrow> le (lt dir2) (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x) 0)"
          proof (cases "x < xr")
            case True
            hence "in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)"
              using `\<forall> x. x < xr \<longrightarrow> in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)`
              by simp
            show ?thesis
            proof (safe)
              assume "coeff (rhs ?eq) x > 0" "0 \<noteq> \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x"
              hence "\<unrhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>\<V> (l' ! sp)\<rangle> x) (UB dir2 (l' ! sp) x)"
                using * `x < xr` `x \<in> rvars_eq ?eq`
                by simp
              hence "le (lt dir2) (\<langle>?bl\<rangle> x) (\<langle>?bp\<rangle> x)"
                using `in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)` `\<B> ?sp = \<B> ?sl` dir2
                apply (auto simp add: bound_compare''_defs)
                using bounds_lg(3)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>u (l ! sl) x" "\<langle>?bl\<rangle> x"]
                using bounds_lg(6)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>l (l ! sl) x" "\<langle>?bl\<rangle> x"]
                unfolding bound_compare''_defs
                by auto
              thus "lt dir2 0 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x)"
                using `0 \<noteq> \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x`
                using minus_gt[of "\<langle>?bl\<rangle> x" "\<langle>?bp\<rangle> x"] minus_lt[of "\<langle>?bp\<rangle> x" "\<langle>?bl\<rangle> x"] dir2
                by auto
            next
              assume "coeff (rhs ?eq) x < 0"  "\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x \<noteq> 0"
              hence "\<unlhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>\<V> (l' ! sp)\<rangle> x) (LB dir2 (l' ! sp) x)"
                using * `x < xr` `x \<in> rvars_eq ?eq`
                by simp
              hence "le (lt dir2) (\<langle>?bp\<rangle> x) (\<langle>?bl\<rangle> x)"
                using `in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)` `\<B> ?sp = \<B> ?sl` dir2
                apply (auto simp add: bound_compare''_defs)
                using bounds_lg(3)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>u (l ! sl) x" "\<langle>?bl\<rangle> x"]
                using bounds_lg(6)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>l (l ! sl) x" "\<langle>?bl\<rangle> x"]
                unfolding bound_compare''_defs
                by auto
              thus "lt dir2 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x) 0"
                using `\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x \<noteq> 0`
                using minus_gt[of "\<langle>?bl\<rangle> x" "\<langle>?bp\<rangle> x"] minus_lt[of "\<langle>?bp\<rangle> x" "\<langle>?bl\<rangle> x"] dir2
                by auto
            qed
          next
            case False
            show ?thesis
            proof (cases "x = xr")
              case True
              have "\<langle>\<V> (l ! (sl + 1))\<rangle> xr = the (LB dir1 ?sl xr)"
                using `l ! sl \<succ> (l ! (sl + 1))`
                using `swap_lr l sl xr`
                using succ_set_on_bound(1)[of "l ! sl" "l ! (sl + 1)" xr]
                using `\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)` dir1
                unfolding bound_compare''_defs
                by auto
              hence "\<langle>?bp\<rangle> xr = the (LB dir1 ?sl xr)"
                using `\<langle>?bp\<rangle> xr = \<langle>\<V> (l ! (sl + 1))\<rangle> xr`
                by simp
              hence "lt dir1 (\<langle>?bl\<rangle> xr) (\<langle>?bp\<rangle> xr)"
                using `LB dir1 ?sl xr \<noteq> None`
                using `\<lhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)` dir1
                by (auto simp add: bound_compare_defs)

              moreover

              have "reasable_var dir2 xr ?eq ?sp"
                using `\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)`
                using `l' ! sp \<succ> (l' ! (sp + 1))`
                using `swap_lr l' sp xs` `swap_rl l' sp xr`
                using succ_min_rvar[of "l' ! sp" "l' ! (sp + 1)"xs xr ?eq] dir2
                unfolding bound_compare''_defs
                by auto
              
              hence "if dir1 = dir2 then coeff (rhs ?eq) xr > 0 else coeff (rhs ?eq) xr < 0"
                using `\<langle>?bp\<rangle> xr = the (LB dir1 ?sl xr)`
                using `\<B> ?sp = \<B> ?sl`[THEN sym] dir1
                using `LB dir1 ?sl xr \<noteq> None` dir1 dir2
                by (auto split: if_splits simp add: bound_compare_defs)
              moreover
              have "dir1 = Positive \<or> dir1 = Negative" "dir2 = Positive \<or> dir2 = Negative"
                using dir1 dir2
                by auto
              ultimately
              show ?thesis
                using `x = xr`
                using minus_lt[of "\<langle>?bp\<rangle> xr" "\<langle>?bl\<rangle> xr"] minus_gt[of "\<langle>?bl\<rangle> xr" "\<langle>?bp\<rangle> xr"]
                by (auto split: if_splits)
            next
              case False
              hence "x > xr"
                using `\<not> x < xr`
                by simp
              hence "\<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x"
                using `\<forall> x \<in> rvars_eq ?eq. x > xr \<longrightarrow> \<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x`
                using `x \<in> rvars_eq ?eq`
                by simp
              thus ?thesis
                by simp
            qed
          qed
        qed
        hence "le (lt dir2) 0 (rhs ?eq \<lbrace> \<lambda> x. \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x \<rbrace>)"
          using dir2
          apply auto
          using valuate_nonneg[of "rhs ?eq" "\<lambda> x. \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x"]
          apply force
          using valuate_nonpos[of "rhs ?eq" "\<lambda> x. \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x"]
          apply force
          done
        hence "le (lt dir2) 0 ((rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace> - (rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>)"
          by (subst valuate_diff)+ simp
        hence "le (lt dir2) ((rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>) ((rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>)"
          using minus_lt[of "(rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>" "(rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>"] dir2
          by auto
        thus ?thesis
          using dir2
          using minus_lt[of "(rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>" "(rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>"]
          using minus_gt[of "(rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>" "(rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>"]
          by auto
      qed
      ultimately
      have False
        using diff_satified dir2
        by (auto split: if_splits)
    }
    thus False
      by auto
  qed
qed

(* -------------------------------------------------------------------------- *)

lemma check_unsat_terminates:
  assumes "\<U> s"
  shows "check_dom s"
by (rule check_dom.intros) (auto simp add: assms)

lemma check_sat_terminates'_aux:
assumes 
  dir: "dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative)" and
  *: "\<And> s'. \<lbrakk>s \<succ> s'; \<nabla> s'; \<triangle> (\<T> s'); \<diamond> s'; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<rbrakk> \<Longrightarrow> check_dom s'" and
  "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
  "\<not> \<U> s" "min_lvar_not_in_bounds s = Some x\<^sub>i" 
  "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)"
shows "check_dom
            (case min_rvar_incdec dir s x\<^sub>i of None \<Rightarrow> s\<lparr>\<U> := True\<rparr>
             | Some x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j (the (LB dir s x\<^sub>i)) s)"
proof (cases "min_rvar_incdec dir s x\<^sub>i")
  case None
  thus ?thesis
    using check_unsat_terminates
    by simp
next
  case (Some x\<^sub>j)
  hence "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
    using min_rvar_incdec_eq_Some_rvars[of _ s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using dir
    by simp
  let ?s' = "pivot_and_update x\<^sub>i x\<^sub>j (the (LB dir s x\<^sub>i)) s"
  have "check_dom ?s'"
  proof (rule * )
    show "s \<succ> ?s'"
      unfolding gt_state_def
      using `\<triangle> (\<T> s)` `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s` `\<nabla> s`
      using `min_lvar_not_in_bounds s = Some x\<^sub>i` `\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)`
        `min_rvar_incdec dir s x\<^sub>i = Some x\<^sub>j` dir
      by auto
  next
    show "\<nabla> ?s'" "\<triangle> (\<T> ?s')" "\<diamond> ?s'" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s'"
      using `min_lvar_not_in_bounds s = Some x\<^sub>i`  Some
      using `\<nabla> s` `\<triangle> (\<T> s)`  `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`  dir
      using pivotandupdate_check_precond
      by auto
  qed
  thus ?thesis
    using Some
    by simp
qed

lemma check_sat_terminates':
  assumes "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "s\<^sub>0 \<succ>\<^sup>* s"
  shows "check_dom s"
using assms
proof (induct s rule: wf_induct[of "{(y, x). s\<^sub>0 \<succ>\<^sup>* x \<and> x \<succ> y}"])
  show "wf {(y, x). s\<^sub>0 \<succ>\<^sup>* x \<and> x \<succ> y}"
  proof (rule finite_acyclic_wf)
    let ?A = "{(s', s). s\<^sub>0 \<succ>\<^sup>* s \<and> s \<succ> s'}" 
    let ?B = "{s. s\<^sub>0 \<succ>\<^sup>* s}"
    have "?A \<subseteq> ?B \<times> ?B"
    proof
      fix p
      assume "p \<in> ?A"
      hence "fst p \<in> ?B" "snd p \<in> ?B"
        using rtrancl_into_trancl1[of s\<^sub>0 "snd p" succ_rel "fst p"]
        by auto
      thus "p \<in> ?B \<times> ?B"
        using mem_Sigma_iff[of "fst p" "snd p"]
        by auto
    qed
    thus "finite ?A"
      using finite_accessible_states[of s\<^sub>0]
      using finite_subset[of ?A "?B \<times> ?B"]
      by simp

    show "acyclic ?A"
    proof-
      have "?A \<subseteq> succ_rel\<inverse>"
        by auto
      thus ?thesis
        using acyclic_converse acyclic_subset
        using acyclic_suc_rel
        by auto
    qed
  qed
next
  fix s
  assume "\<forall> s'. (s', s) \<in> {(y, x). s\<^sub>0 \<succ>\<^sup>* x \<and> x \<succ> y} \<longrightarrow> \<nabla> s' \<longrightarrow> \<triangle> (\<T> s') \<longrightarrow> \<diamond> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<longrightarrow> s\<^sub>0 \<succ>\<^sup>* s' \<longrightarrow> check_dom s'" 
           "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" " \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "s\<^sub>0 \<succ>\<^sup>* s"
  hence *: "\<And> s'. \<lbrakk>s \<succ> s'; \<nabla> s'; \<triangle> (\<T> s'); \<diamond> s'; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<rbrakk> \<Longrightarrow> check_dom s'"
    using rtrancl_into_trancl1[of s\<^sub>0 s succ_rel]
    using trancl_into_rtrancl[of s\<^sub>0 _ succ_rel]
    by auto
  show "check_dom s"
  proof (rule check_dom.intros, simp_all add: check'_def, unfold Positive_def[symmetric], unfold Negative_def[symmetric])
    fix x\<^sub>i
    assume "\<not> \<U> s" "Some x\<^sub>i = min_lvar_not_in_bounds s" "\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i"
    have "\<B>\<^sub>l s x\<^sub>i = LB Positive s x\<^sub>i"
      by simp
    show "check_dom
            (case min_rvar_incdec Positive s x\<^sub>i of
             None \<Rightarrow> s\<lparr>\<U> := True\<rparr>
             | Some x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j (the (\<B>\<^sub>l s x\<^sub>i)) s)"
      apply (subst `\<B>\<^sub>l s x\<^sub>i = LB Positive s x\<^sub>i`)
      apply (rule check_sat_terminates'_aux[of Positive s x\<^sub>i])
      using `\<nabla> s` `\<triangle> (\<T> s)`  `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s` *
      using `\<not> \<U> s` `Some x\<^sub>i = min_lvar_not_in_bounds s` `\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i`
      by (simp_all add: bound_compare''_defs)
  next
    fix x\<^sub>i
    assume "\<not> \<U> s" "Some x\<^sub>i = min_lvar_not_in_bounds s" "\<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i"
    hence "\<langle>\<V> s\<rangle> x\<^sub>i >\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i"
      using min_lvar_not_in_bounds_Some[of s x\<^sub>i]
      using neg_bounds_compare(7) neg_bounds_compare(2)
      by auto
    have "\<B>\<^sub>u s x\<^sub>i = LB Negative s x\<^sub>i"
      by simp
    show "check_dom
            (case min_rvar_incdec Negative s x\<^sub>i of
             None \<Rightarrow> s\<lparr>\<U> := True\<rparr>
             | Some x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j (the (\<B>\<^sub>u s x\<^sub>i)) s)"
      apply (subst `\<B>\<^sub>u s x\<^sub>i = LB Negative s x\<^sub>i`)
      apply (rule check_sat_terminates'_aux)
      using `\<nabla> s` `\<triangle> (\<T> s)`  `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s` *
      using `\<not> \<U> s` `Some x\<^sub>i = min_lvar_not_in_bounds s` `\<langle>\<V> s\<rangle> x\<^sub>i >\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i` `\<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i`
      by (simp_all add: bound_compare''_defs)
  qed
qed

lemma check_sat_terminates:
  assumes "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
  shows "check_dom s"
using assms
using check_sat_terminates'[of s s]
by simp
(*>*)
(*<*)
lemma check_cases:
  assumes "\<U> s \<Longrightarrow> P s"
  assumes "\<lbrakk>\<not> \<U> s; min_lvar_not_in_bounds s = None\<rbrakk> \<Longrightarrow> P s"
  assumes "\<And> x\<^sub>i dir. 
    \<lbrakk>dir = Positive \<or> dir = Negative;
     \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i;
     \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i);
     min_rvar_incdec dir s x\<^sub>i = None\<rbrakk> \<Longrightarrow> 
        P (s\<lparr>\<U> := True\<rparr>)"
  assumes "\<And> x\<^sub>i x\<^sub>j l\<^sub>i dir. 
    \<lbrakk>dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative);
     \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i;
     \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i); 
     min_rvar_incdec dir s x\<^sub>i = Some x\<^sub>j;
     l\<^sub>i = the (LB dir s x\<^sub>i);
     check' dir x\<^sub>i s = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s\<rbrakk> \<Longrightarrow> 
        P (check (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s))"
  assumes "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
  shows "P (check s)"
proof (cases "\<U> s")
  case True
  thus ?thesis
    using assms(1)
    using check.simps[of s]
    by simp
next
  case False
  show ?thesis
  proof (cases "min_lvar_not_in_bounds s")
    case None
    thus ?thesis
      using `\<not> \<U> s`
      using assms(2) `\<triangle> (\<T> s)` `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`
      using check.simps[of s]
      by simp
  next
    case (Some x\<^sub>i)
    let ?dir = "if (\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i) then Positive else Negative"
    let ?s' = "check' ?dir x\<^sub>i s"
    have "\<lhd>\<^sub>l\<^sub>b (lt ?dir) (\<langle>\<V> s\<rangle> x\<^sub>i)  (LB ?dir s x\<^sub>i)"
      using `min_lvar_not_in_bounds s = Some x\<^sub>i`
      using min_lvar_not_in_bounds_Some[of s x\<^sub>i]
      using not_in_bounds[of x\<^sub>i "\<langle>\<V> s\<rangle>" "\<B>\<^sub>l s" "\<B>\<^sub>u s"]
      by (auto split: if_splits simp add: bound_compare''_defs)

    have "P (check ?s')"
      apply (rule check'_cases)
      using `\<not> \<U> s` `min_lvar_not_in_bounds s = Some x\<^sub>i` `\<lhd>\<^sub>l\<^sub>b (lt ?dir) (\<langle>\<V> s\<rangle> x\<^sub>i)  (LB ?dir s x\<^sub>i)`
      using assms(3)[of ?dir x\<^sub>i]
      using assms(4)[of ?dir x\<^sub>i]
      using check.simps[of "s\<lparr>\<U> := True\<rparr>"]
      using `\<triangle> (\<T> s)` `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`
      by (auto simp add:  bounds_consistent_def  curr_val_satisfies_no_lhs_def)
    thus ?thesis
      using `\<not> \<U> s` `min_lvar_not_in_bounds s = Some x\<^sub>i`
      using check.simps[of s]
      using `\<triangle> (\<T> s)` `\<diamond> s` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s`
      by auto
  qed
qed
(*>*)
(*<*)
lemma check_induct:
  fixes s :: "'a state"
  assumes *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  assumes **:
  "\<And> s. \<U> s \<Longrightarrow> P s s"
  "\<And> s. \<lbrakk>\<not> \<U> s; min_lvar_not_in_bounds s = None\<rbrakk> \<Longrightarrow> P s s"
  "\<And> s x\<^sub>i dir. \<lbrakk>dir = Positive \<or> dir = Negative; \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i; \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i); min_rvar_incdec dir s x\<^sub>i = None\<rbrakk> \<Longrightarrow> P s (s\<lparr>\<U> := True\<rparr>)"
  assumes step': "\<And> s x\<^sub>i x\<^sub>j l\<^sub>i. \<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<rbrakk> \<Longrightarrow> P s (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
  assumes trans': "\<And> si sj sk. \<lbrakk>P si sj; P sj sk\<rbrakk> \<Longrightarrow> P si sk"
  shows "P s (check s)"
proof-
  have "check_dom s"
    using *
    by (simp add: check_sat_terminates)
  thus ?thesis
    using *
  proof (induct s rule: check_dom.induct)
    case (step s')
    show ?case
    proof (rule check_cases)
      fix x\<^sub>i x\<^sub>j l\<^sub>i dir
      let ?dir = "if \<langle>\<V> s'\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s' x\<^sub>i then Positive else Negative"
      let ?s' = "check' dir x\<^sub>i s'"
      assume "\<not> \<U> s'" "min_lvar_not_in_bounds s' = Some x\<^sub>i" "min_rvar_incdec dir s' x\<^sub>i = Some x\<^sub>j" "l\<^sub>i = the (LB dir s' x\<^sub>i)"
        "?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'" "dir = ?dir"
      moreover
      hence "\<nabla> ?s'" "\<triangle> (\<T> ?s')" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s'" "\<diamond> ?s'"
        using `\<nabla> s'` `\<triangle> (\<T> s')` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'` `\<diamond> s'`
        using `?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'`
        using pivotandupdate_check_precond[of dir s' x\<^sub>i x\<^sub>j l\<^sub>i]
        by auto
      ultimately
      have "P (check' dir x\<^sub>i s') (check (check' dir x\<^sub>i s'))"
        using step(2)[of x\<^sub>i] step(4)[of x\<^sub>i] `\<triangle> (\<T> s')` `\<nabla> s'`
        by auto
      thus "P s' (check (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'))"
        using `?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'` `\<triangle> (\<T> s')` `\<nabla> s'` 
        using `min_lvar_not_in_bounds s' = Some x\<^sub>i` `min_rvar_incdec dir s' x\<^sub>i = Some x\<^sub>j`
        using step'[of s' x\<^sub>i x\<^sub>j l\<^sub>i]
        using trans'[of s' ?s' "check ?s'"]
        by (auto simp add: min_lvar_not_in_bounds_lvars  min_rvar_incdec_eq_Some_rvars)
    qed (simp_all add: `\<nabla> s'` `\<triangle> (\<T> s')` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'` `\<diamond> s'` **)
  qed
qed

lemma check_induct':
  fixes s :: "'a state"
  assumes "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  assumes "\<And> s x\<^sub>i dir. \<lbrakk>dir = Positive \<or> dir = Negative; \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i; \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i); min_rvar_incdec dir s x\<^sub>i = None; P s\<rbrakk> \<Longrightarrow> P (s\<lparr>\<U> := True\<rparr>)"
  assumes "\<And> s x\<^sub>i x\<^sub>j l\<^sub>i. \<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i); P s\<rbrakk> \<Longrightarrow> P (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
  assumes "P s"
  shows "P (check s)"
proof-
  have "P s \<longrightarrow> P (check s)"
    by (rule check_induct) (simp_all add: assms)
  thus ?thesis
    using `P s`
    by simp
qed

lemma check_induct'':
  fixes s :: "'a state"
  assumes *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  assumes **: 
    "\<U> s \<Longrightarrow> P s"
    "\<And> s. \<lbrakk>\<nabla> s; \<triangle> (\<T> s); \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<not> \<U> s; min_lvar_not_in_bounds s = None\<rbrakk> \<Longrightarrow> P s"
    "\<And> s x\<^sub>i dir. \<lbrakk>dir = Positive \<or> dir = Negative; \<nabla> s; \<triangle> (\<T> s); \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s;  \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i; \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i); min_rvar_incdec dir s x\<^sub>i = None\<rbrakk> \<Longrightarrow> P (s\<lparr>\<U> := True\<rparr>)"
  shows "P (check s)"
proof (cases "\<U> s")
  case True
  thus ?thesis
    using `\<U> s \<Longrightarrow> P s`
    by (simp add: check.simps)
next
  case False
  have "check_dom s"
    using *
    by (simp add: check_sat_terminates)
  thus ?thesis
    using * False
  proof (induct s rule: check_dom.induct)
    case (step s')
    show ?case
    proof (rule check_cases)
      fix x\<^sub>i x\<^sub>j l\<^sub>i dir
      let ?dir = "if \<langle>\<V> s'\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s' x\<^sub>i then Positive else Negative"
      let ?s' = "check' dir x\<^sub>i s'"
      assume "\<not> \<U> s'" "min_lvar_not_in_bounds s' = Some x\<^sub>i" "min_rvar_incdec dir s' x\<^sub>i = Some x\<^sub>j" "l\<^sub>i = the (LB dir s' x\<^sub>i)"
        "?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'" "dir = ?dir"
      moreover
      hence "\<nabla> ?s'" "\<triangle> (\<T> ?s')" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s'" "\<diamond> ?s'" "\<not> \<U> ?s'"
        using `\<nabla> s'` `\<triangle> (\<T> s')` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'` `\<diamond> s'`
        using `?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'`
        using pivotandupdate_check_precond[of dir s' x\<^sub>i x\<^sub>j l\<^sub>i] 
        using pivotandupdate_unsat_id[of s' x\<^sub>i x\<^sub>j l\<^sub>i]
        by (auto simp add: min_lvar_not_in_bounds_lvars  min_rvar_incdec_eq_Some_rvars)
      ultimately
      have "P (check (check' dir x\<^sub>i s'))"
        using step(2)[of x\<^sub>i] step(4)[of x\<^sub>i] `\<triangle> (\<T> s')` `\<nabla> s'`
        by auto
      thus "P (check (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'))"
        using `?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'` 
        by simp
    qed (simp_all add: `\<nabla> s'` `\<triangle> (\<T> s')` `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'` `\<diamond> s'` `\<not> \<U> s'` ** )
  qed
qed
(*>*)
(*<*)
end
(*>*)
(*<*)
sublocale PivotUpdateMinVars < Check check
proof
  fix s :: "'a state"
  assume "\<U> s"
  thus "check s = s"
    by (simp add: check.simps)
next
  fix s :: "'a state" and v :: "'a valuation"
  assume *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  hence "v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> (check s)"
    by (rule check_induct, simp_all add: pivotandupdate_tableau_equiv)
  moreover
  have "\<triangle> (\<T> (check s))"
    by (rule check_induct', simp_all add: * pivotandupdate_tableau_normalized)
  moreover
  have "\<nabla> (check s)"
  proof (rule check_induct', simp_all add: * pivotandupdate_tableau_valuated)
    fix s
    assume "\<nabla> s" 
    thus "\<nabla> (s\<lparr>\<U> := True\<rparr>)"
      by (simp add: tableau_valuated_def)
  qed
  ultimately
  show "let s' = check s in v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s' \<and> \<triangle> (\<T> s') \<and> \<nabla> s'"
    by (simp add: Let_def)
next
  fix s :: "'a state"
  assume *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  thus "\<B> (check s) = \<B> s"
    by (rule check_induct, simp_all add: pivotandupdate_bounds_id)
next
  fix s :: "'a state"
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
  show "\<not> \<U> (check s) \<longrightarrow> \<Turnstile> (check s)"
  proof (rule check_induct'', simp_all add: *)
    fix s
    assume "min_lvar_not_in_bounds s = None" "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
    thus " \<Turnstile> s"
      using min_lvar_not_in_bounds_None[of s]
      unfolding curr_val_satisfies_state_def satisfies_state_def
      unfolding curr_val_satisfies_no_lhs_def
      by (auto simp add: satisfies_bounds_set.simps satisfies_bounds.simps)
  qed
next
  fix s :: "'a state"
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
  show "\<U> (check s) \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s check s)" (is "?P (check s)")
  proof (rule check_induct'')
    fix s' :: "'a state" and x\<^sub>i dir
    assume "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'" "min_rvar_incdec dir s' x\<^sub>i = None" "\<not> \<U> s'" "min_lvar_not_in_bounds s' = Some x\<^sub>i" "dir = Positive \<or> dir = Negative" "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s'\<rangle> x\<^sub>i) (LB dir s' x\<^sub>i)"
    show "\<U> (s'\<lparr>\<U> := True\<rparr>) \<longrightarrow> \<not> (\<exists>v. v \<Turnstile>\<^sub>s s'\<lparr>\<U> := True\<rparr>)"
    proof
      have "\<not> (\<exists> v. v \<Turnstile>\<^sub>s s')"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain v where "v \<Turnstile>\<^sub>s s'"
          by auto

        let ?eq = "eq_for_lvar (\<T> s') x\<^sub>i"

        have "x\<^sub>i \<in> lvars (\<T> s')"
          using `min_lvar_not_in_bounds s' = Some x\<^sub>i`
          by (simp add: min_lvar_not_in_bounds_lvars)
        hence "?eq \<in> set (\<T> s')" "lhs ?eq = x\<^sub>i"
          by (auto simp add: eq_for_lvar)

        have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>e ?eq"
          using `\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'` `?eq \<in> set (\<T> s')`
          unfolding curr_val_satisfies_no_lhs_def
          by (simp add: satisfies_tableau_def)
        hence "\<langle>\<V> s'\<rangle> x\<^sub>i = (rhs ?eq) \<lbrace> \<langle>\<V> s'\<rangle> \<rbrace>"
          using `lhs ?eq = x\<^sub>i`
          by (simp add: satisfies_eq_def)

        moreover

        have "v \<Turnstile>\<^sub>e ?eq"
          using `v \<Turnstile>\<^sub>s s'` `?eq \<in> set (\<T> s')`
          by (simp add: satisfies_state_def satisfies_tableau_def)
        hence "v x\<^sub>i = (rhs ?eq) \<lbrace> v \<rbrace>"
          using `lhs ?eq = x\<^sub>i`
          by (simp add: satisfies_eq_def)

        moreover

        have "\<unrhd>\<^sub>l\<^sub>b (lt dir) (v x\<^sub>i) (LB dir s' x\<^sub>i)"
          using `v \<Turnstile>\<^sub>s s'`
          using `dir = Positive \<or> dir = Negative`
          by (auto simp add: satisfies_state_def satisfies_bounds.simps bound_compare''_defs)
        
        moreover

        have "le (lt dir) (rhs (?eq) \<lbrace>v\<rbrace>) (rhs (?eq) \<lbrace> \<langle>\<V> s'\<rangle> \<rbrace>)"
          using min_rvar_incdec_eq_None' `dir = Positive \<or> dir = Negative`
          using `min_rvar_incdec dir s' x\<^sub>i = None` `v \<Turnstile>\<^sub>s s'`
          by (simp add: Let_def satisfies_state_def)

        moreover

        obtain l\<^sub>i where "LB dir s' x\<^sub>i = Some l\<^sub>i" "lt dir (\<langle>\<V> s'\<rangle> x\<^sub>i) l\<^sub>i"
          using `\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s'\<rangle> x\<^sub>i) (LB dir s' x\<^sub>i)`
          by (cases "LB dir s' x\<^sub>i") (auto simp add: bound_compare_defs)

        ultimately

        show False
          using `dir = Positive \<or> dir = Negative`
          by (auto simp add: bound_compare_defs)
      qed
      thus "\<not> (\<exists>v. v \<Turnstile>\<^sub>s s'\<lparr>\<U> := True\<rparr>)"
        by (simp add: satisfies_state_def)
    qed
  qed (simp_all add: *)
qed
(*>*)
subsection{* Symmetries  *}

text{* \label{sec:symmetries} Simplex algorithm exhibits many
symmetric cases. For example, @{text "assert_bound"} treats atoms
@{text "Leq x c"} and @{text "Geq x c"} in a symmetric manner, @{text
"check_inc"} and @{text "check_dec"} are symmetric, etc. These
symmetric cases differ only in several aspects: order relations
between numbers (@{text "<"} vs @{text ">"} and @{text "\<le>"} vs @{text
"\<ge>"}), the role of lower and upper bounds (@{text "\<B>\<^sub>l"} vs
@{text "\<B>\<^sub>u"}) and their updating functions, comparisons with bounds
(e.g., @{text "\<ge>\<^sub>u\<^sub>b"} vs @{text "\<le>\<^sub>l\<^sub>b"} or
@{text "<\<^sub>l\<^sub>b"} vs @{text ">\<^sub>u\<^sub>b"}), and atom constructors (@{text "Leq"}
and @{text "Geq"}). These can be attributed to two different
orientations (positive and negative) of rational axis. To avoid
duplicating definitions and proofs, @{text "assert_bound"} definition
cases for @{text "Leq"} and @{text "Geq"} are replaced by a call to a
newly introduced function parametrized by a @{text "Direction"} --- a
record containing minimal set of aspects listed above that differ in
two definition cases such that other aspects can be derived from them
(e.g., only @{text "<"} need to be stored while @{text "\<le>"} can be
derived from it). Two constants of the type @{text "Direction"} are
defined: @{text "Positive"} (with @{text "<"}, @{text "\<le>"} orders,
@{text "\<B>\<^sub>l"} for lower and @{text "\<B>\<^sub>u"} for upper bounds and their
corresponding updating functions, and @{text "Leq"} constructor) and
@{text "Negative"} (completely opposite from the previous
one). Similarly, @{text "check_inc"} and @{text "check_dec"} are
replaced by a new function @{text "check_incdec"} parametrized by a
@{text "Direction"}. All lemmas, previously repeated for each
symmetric instance, were replaced by a more abstract one, again
parametrized by a @{text "Direction"} parameter. 
\vspace{-3mm}
*} 
(*<*) 
(*-------------------------------------------------------------------------- *)
subsection{* Concrete implementation *} 
(*-------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Init init_state *)
(* -------------------------------------------------------------------------- *)

text{* It is easy to give a concrete implementation of the initial
state constructor, which satisfies the specification of the @{term
Init} locale.  For example:*}
(*<*) definition init_state where (*>*)
  "init_state t \<equiv> \<lparr> \<T> = t, \<B>\<^sub>l = Map.empty, \<B>\<^sub>u = Map.empty, 
                    \<V> = Mapping.tabulate (vars_list t) (\<lambda> v. 0::'a::zero), \<U> = False  \<rparr>"

interpretation Init init_state
proof
  fix t
  show "\<langle>\<V> ((init_state t)::'a state)\<rangle> \<Turnstile>\<^sub>t t"
    unfolding satisfies_tableau_def satisfies_eq_def
  proof (safe)
    fix l r
    assume "(l, r) \<in> set t"
    hence "l \<in> set (vars_list t)" "vars r \<subseteq> set (vars_list t)"
      by (auto simp: set_vars_list) (transfer, force)
    hence *: "vars r \<subseteq> lhs ` set t \<union> (\<Union>x\<in>set t. rvars_eq x)" by (auto simp: set_vars_list)
    have "\<langle>\<V> (init_state t)\<rangle> l = (0::'a)"
      using `l \<in> set (vars_list t)`
      unfolding init_state_def by (auto simp: map2fun_def lookup_tabulate)
    moreover
    have "r \<lbrace> \<langle>\<V> (init_state t)\<rangle> \<rbrace> = (0::'a)" using *
    proof (transfer, goal_cases)
      case (1 r t)
      {
        fix x
        assume "x\<in>{v. r v \<noteq> 0}"
        hence "r x *R \<langle>\<V> (init_state t)\<rangle> x = (0::'a)"
          using 1
          unfolding init_state_def
          by (auto simp add: map2fun_def lookup_tabulate comp_def restrict_map_def set_vars_list AbstractLinearPoly.vars_def)
      }
      thus ?case by auto
    qed
    ultimately
    show "\<langle>\<V> ((init_state t)::'a state)\<rangle> (lhs (l, r)) = rhs (l, r) \<lbrace> \<langle>\<V> (init_state t)\<rangle> \<rbrace>"
      by auto
    qed
next
  fix t
  show "\<nabla> (init_state t)"
    unfolding init_state_def
    by (auto simp add: lookup_tabulate tableau_valuated_def comp_def restrict_map_def set_vars_list lvars_def rvars_def)
qed (simp_all add: init_state_def)
(*>*)
(*<*)
(* -------------------------------------------------------------------------- *)
(* MinVars min_lvar_not_in_bounds min_rvar_incdec_eq *)
(* -------------------------------------------------------------------------- *)
definition min_lvar_not_in_bounds :: "'a::{linorder,zero} state \<Rightarrow> var option" where
  "min_lvar_not_in_bounds s \<equiv>
      min_satisfying  (\<lambda> x. \<not> in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s)) (map lhs (\<T> s))"

interpretation MinLVarNotInBounds min_lvar_not_in_bounds
proof
  fix s::"'a state"
  show "min_lvar_not_in_bounds s = None \<longrightarrow>
        (\<forall>x\<in>lvars (\<T> s). in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s))"
    unfolding min_lvar_not_in_bounds_def lvars_def
    using min_satisfying_None
    by blast
next
  fix s x\<^sub>i
  show "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> x\<^sub>i \<in> lvars (\<T> s) \<and> 
                                              \<not> in_bounds x\<^sub>i \<langle>\<V> s\<rangle> (\<B> s) \<and> 
                                              (\<forall>x\<in>lvars (\<T> s). x < x\<^sub>i \<longrightarrow> in_bounds x \<langle>\<V> s\<rangle> (\<B> s))"
    unfolding min_lvar_not_in_bounds_def lvars_def
    using min_satisfying_Some
    by blast+
qed

definition min_rvar_incdec_eq :: "'a Direction \<Rightarrow> 'a::lrv state \<Rightarrow> eq \<Rightarrow> var option" where
"min_rvar_incdec_eq dir s eq \<equiv>
  min_satisfying (\<lambda> x. reasable_var dir x eq s) (AbstractLinearPoly.vars_list (rhs eq))"

interpretation MinRVarsEq min_rvar_incdec_eq
proof
  fix s eq dir
  show "min_rvar_incdec_eq dir s eq = None \<longrightarrow> 
    (\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s)"
    unfolding min_rvar_incdec_eq_def
    using min_satisfying_None set_vars_list
    by blast

  fix x\<^sub>j
  show "min_rvar_incdec_eq dir s eq = Some x\<^sub>j \<longrightarrow> x\<^sub>j \<in> rvars_eq eq"
       "min_rvar_incdec_eq dir s eq = Some x\<^sub>j \<longrightarrow> reasable_var dir x\<^sub>j eq s"
       "min_rvar_incdec_eq dir s eq = Some x\<^sub>j \<longrightarrow> 
          (\<forall> x' \<in> rvars_eq eq. x' < x\<^sub>j \<longrightarrow> \<not> reasable_var dir x' eq s)"
    unfolding min_rvar_incdec_eq_def
    using min_satisfying_Some set_vars_list
    by blast+
qed

(* -------------------------------------------------------------------------- *)
(* EqForLVar eq_idx_for_lvar *)
(* -------------------------------------------------------------------------- *)

primrec eq_idx_for_lvar_aux :: "tableau \<Rightarrow> var \<Rightarrow> nat \<Rightarrow> nat" where
  "eq_idx_for_lvar_aux [] x i = i"
| "eq_idx_for_lvar_aux (eq # t) x i = 
     (if lhs eq = x then i else eq_idx_for_lvar_aux t x (i+1))"

definition eq_idx_for_lvar where
"eq_idx_for_lvar t x \<equiv> eq_idx_for_lvar_aux t x 0"

lemma eq_idx_for_lvar_aux:
assumes "x \<in> lvars t" 
shows "let idx = eq_idx_for_lvar_aux t x i in
            i \<le> idx \<and> idx < i + length t \<and> lhs (t ! (idx - i)) = x"
using assms
proof (induct t arbitrary: i)
  case Nil
  thus ?case
    by (simp add: lvars_def)
next
  case (Cons eq t)
  show ?case
    using Cons(1)[of "i+1"] Cons(2)
    by (cases "x = lhs eq") (auto simp add: Let_def lvars_def nth_Cons')
qed

global_interpretation EqForLVarDefault: EqForLVar eq_idx_for_lvar 
  defines eq_for_lvar_code = EqForLVarDefault.eq_for_lvar
proof (unfold_locales)
  fix x t
  assume "x \<in> lvars t"
  thus "eq_idx_for_lvar t x < length t \<and>
          lhs (t ! eq_idx_for_lvar t x) = x"
    using eq_idx_for_lvar_aux[of x t 0]
    by (simp add: Let_def  eq_idx_for_lvar_def)
qed

(* -------------------------------------------------------------------------- *)
(* PivotEq pivot_eq *)
(* -------------------------------------------------------------------------- *)

definition pivot_eq :: "eq \<Rightarrow> var \<Rightarrow> eq" where
  "pivot_eq e y \<equiv> let cy = coeff (rhs e) y in
     (y, (-1/cy) *R ((rhs e) - cy *R (Var y)) + (1/cy) *R (Var (lhs e)))"

lemma pivot_eq_satisfies_eq:
  assumes "y \<in> rvars_eq e"
  shows "v \<Turnstile>\<^sub>e e = v \<Turnstile>\<^sub>e pivot_eq e y"
  using assms
  using scaleRat_right_distrib[of "1 / Rep_linear_poly (rhs e) y" "- (rhs e \<lbrace> v \<rbrace>)" "v (lhs e)"]
  using Groups.group_add_class.minus_unique[of "- ((rhs e) \<lbrace> v \<rbrace>)" "v (lhs e)"]
  unfolding coeff_def vars_def
  by (simp add: coeff_def vars_def Let_def pivot_eq_def satisfies_eq_def)
     (auto simp add: rational_vector.scale_right_diff_distrib valuate_add valuate_minus valuate_uminus valuate_scaleRat valuate_Var)

lemma pivot_eq_rvars: 
  assumes "x \<in> vars (rhs (pivot_eq e v))" "x \<noteq> lhs e" "coeff (rhs e) v \<noteq> 0" "v \<noteq> lhs e"
  shows "x \<in> vars (rhs e)"
proof-
  have "v \<notin> vars ((1 / coeff (rhs e) v) *R (rhs e - coeff (rhs e) v *R Var v))"
    using coeff_zero
    by force
  hence "x \<noteq> v"
    using assms(1) assms(3) assms(4)
    using vars_plus[of "(-1 / coeff (rhs e) v) *R (rhs e - coeff (rhs e) v *R Var v)" "(1 / coeff (rhs e) v) *R Var (lhs e)"]
    by (auto simp add: Let_def vars_scaleRat pivot_eq_def)
  thus ?thesis
    using assms
    using vars_plus[of "(-1 / coeff (rhs e) v) *R (rhs e - coeff (rhs e) v *R Var v)" "(1 / coeff (rhs e) v) *R Var (lhs e)"]
    using vars_minus[of "rhs e" "coeff (rhs e) v *R Var v"]
    by (auto simp add: vars_scaleRat Let_def pivot_eq_def)
qed

interpretation PivotEq pivot_eq
proof
  fix eq x\<^sub>j
  assume "x\<^sub>j \<in> rvars_eq eq" "lhs eq \<notin> rvars_eq eq"
  have "lhs (pivot_eq eq x\<^sub>j) = x\<^sub>j"
    unfolding pivot_eq_def
    by (simp add: Let_def)
  moreover
  have "rvars_eq (pivot_eq eq x\<^sub>j) =
          {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
  proof
    show "rvars_eq (pivot_eq eq x\<^sub>j) \<subseteq> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
    proof
      fix x
      assume "x \<in> rvars_eq (pivot_eq eq x\<^sub>j)"
      have *: "coeff (rhs (pivot_eq eq x\<^sub>j)) x\<^sub>j = 0"
        using `x\<^sub>j \<in> rvars_eq eq` `lhs eq \<notin> rvars_eq eq`
        using coeff_Var2[of "lhs eq" x\<^sub>j]
        by (auto simp add: Let_def pivot_eq_def)
      have "coeff (rhs eq) x\<^sub>j \<noteq> 0"
        using `x\<^sub>j \<in> rvars_eq eq`
        using coeff_zero
        by (cases eq) (auto simp add:)
      thus "x \<in> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
        using pivot_eq_rvars[of x eq x\<^sub>j]
        using `x \<in> rvars_eq (pivot_eq eq x\<^sub>j)` `x\<^sub>j \<in> rvars_eq eq` `lhs eq \<notin> rvars_eq eq`
        using coeff_zero *
        by auto
    qed
    show "{lhs eq} \<union> (rvars_eq eq - {x\<^sub>j}) \<subseteq> rvars_eq (pivot_eq eq x\<^sub>j)"
    proof
      fix x
      assume "x \<in> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
      have *: "coeff (rhs eq) (lhs eq) = 0"
        using coeff_zero
        using `lhs eq \<notin> rvars_eq eq`
        by auto
      have **: "coeff (rhs eq) x\<^sub>j \<noteq> 0"
        using `x\<^sub>j \<in> rvars_eq eq`
        by (simp add: coeff_zero)
      have ***: "x \<in> rvars_eq eq \<Longrightarrow> coeff (Var (lhs eq)) x = 0"
        using `lhs eq \<notin> rvars_eq eq`
        using coeff_Var2[of "lhs eq" x]
        by auto
      have "coeff (Var x\<^sub>j) (lhs eq) = 0"
        using `x\<^sub>j \<in> rvars_eq eq` `lhs eq \<notin> rvars_eq eq`
        using coeff_Var2[of x\<^sub>j "lhs eq"]
        by auto
      hence "coeff (rhs (pivot_eq eq x\<^sub>j)) x \<noteq> 0"
        using `x \<in> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})` * ** ***
        using coeff_zero[of "rhs eq" x]
        by (auto simp add: Let_def coeff_Var2 pivot_eq_def)
      thus "x \<in> rvars_eq (pivot_eq eq x\<^sub>j)"
        by (simp add: coeff_zero)
    qed
  qed
  ultimately
  show "let eq' = pivot_eq eq x\<^sub>j in lhs eq' = x\<^sub>j \<and> rvars_eq eq' = {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
    by (simp add: Let_def)
next
  fix v eq x\<^sub>j
  assume "x\<^sub>j \<in> rvars_eq eq"
  thus "v \<Turnstile>\<^sub>e pivot_eq eq x\<^sub>j = v \<Turnstile>\<^sub>e eq"
    using pivot_eq_satisfies_eq
    by blast
qed

(* -------------------------------------------------------------------------- *)
(* SubstVar subst_var  *)
(* -------------------------------------------------------------------------- *)

definition subst_var:: "var \<Rightarrow> linear_poly \<Rightarrow> linear_poly \<Rightarrow> linear_poly" where
  "subst_var v lp' lp \<equiv> lp + (coeff lp v) *R lp' - (coeff lp v) *R (Var v)"

definition
  [simp]: "subst_var_eq_code = SubstVar.subst_var_eq subst_var"

global_interpretation SubstVar subst_var rewrites  
  "SubstVar.subst_var_eq subst_var = subst_var_eq_code"
proof (unfold_locales)
  fix x\<^sub>j lp' lp
  have *: "\<And>x. \<lbrakk>x \<in> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j); x \<notin> vars lp'\<rbrakk> \<Longrightarrow> x \<in> vars lp"
  proof-
    fix x
    assume "x \<in> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j)"
    hence "coeff (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j) x \<noteq> 0"
      using linpoly_coeff
      by force
    assume "x \<notin> vars lp'"
    hence "coeff lp' x = 0"
      using linpoly_coeff
      by auto
    show "x \<in> vars lp"
    proof(rule ccontr)
      assume "x \<notin> vars lp"
      hence "coeff lp x = 0"
        using linpoly_coeff
        by auto
      thus False
        using `coeff (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j) x \<noteq> 0`
        using `coeff lp' x = 0`
        by (cases "x = x\<^sub>j") (auto simp add: coeff_Var2)
    qed
  qed
  have "vars (subst_var x\<^sub>j lp' lp) \<subseteq> (vars lp - {x\<^sub>j}) \<union> vars lp'"
    unfolding subst_var_def
    using linpoly_coeff[of "lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j" x\<^sub>j]
    using linpoly_coeff[of lp' x\<^sub>j]
    using *
    by auto
  moreover
  have "\<And>x. \<lbrakk>x \<notin> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j); x \<in> vars lp; x \<notin> vars lp'\<rbrakk> \<Longrightarrow> x = x\<^sub>j"
  proof-
    fix x
    assume "x \<in> vars lp" "x \<notin> vars lp'"
    hence "coeff lp x \<noteq> 0" "coeff lp' x = 0"
      using linpoly_coeff
      by auto
    assume "x \<notin> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j)"
    hence "coeff (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j) x = 0"
      using linpoly_coeff
      by force
    thus "x = x\<^sub>j"
      using `coeff lp x \<noteq> 0` `coeff lp' x = 0`
      by (cases "x = x\<^sub>j") (auto simp add: coeff_Var2)
  qed
  hence "vars lp - {x\<^sub>j} - vars lp' \<subseteq> vars (subst_var x\<^sub>j lp' lp)"
    by (auto simp add: subst_var_def)
  ultimately show "vars lp - {x\<^sub>j} - vars lp' \<subseteq>s vars (subst_var x\<^sub>j lp' lp)
       \<subseteq>s vars lp - {x\<^sub>j} \<union> vars lp'"
    by simp
next
  fix v x\<^sub>j lp' lp
  show "v x\<^sub>j = lp' \<lbrace> v \<rbrace> \<longrightarrow> lp \<lbrace> v \<rbrace> = (subst_var x\<^sub>j lp' lp) \<lbrace> v \<rbrace>"
    unfolding subst_var_def
    using valuate_minus[of "lp + coeff lp x\<^sub>j *R lp'" "coeff lp x\<^sub>j *R Var x\<^sub>j" v]
    using valuate_add[of lp "coeff lp x\<^sub>j *R lp'" v]
    using valuate_scaleRat[of "coeff lp x\<^sub>j" lp' v] valuate_scaleRat[of "coeff lp x\<^sub>j" "Var x\<^sub>j" v]
    using valuate_Var[of x\<^sub>j v]
    by auto
qed simp_all

(* -------------------------------------------------------------------------- *)
(* Update update  *)
(* -------------------------------------------------------------------------- *)

definition rhs_eq_val where
"rhs_eq_val v x\<^sub>i c e \<equiv> let x\<^sub>j = lhs e; a\<^sub>i\<^sub>j = coeff (rhs e) x\<^sub>i in
      \<langle>v\<rangle> x\<^sub>j + a\<^sub>i\<^sub>j *R (c - \<langle>v\<rangle> x\<^sub>i)"

global_interpretation RhsEqValDefault: RhsEqVal rhs_eq_val 
  defines
    update_code = RhsEqValDefault.update and
    assert_bound'_code = RhsEqValDefault.assert_bound' and
    assert_bound_code = RhsEqValDefault.assert_bound
  rewrites
    "RhsEqVal.update rhs_eq_val = update_code" and
    "Update.assert_bound update_code = assert_bound_code" and
    "Update.assert_bound' update_code = assert_bound'_code"
proof (unfold_locales)
  fix v x c e
  assume "\<langle>v\<rangle> \<Turnstile>\<^sub>e e" 
  thus "rhs_eq_val v x c e = rhs e \<lbrace> \<langle>v\<rangle>(x := c) \<rbrace>"
    unfolding rhs_eq_val_def Let_def
    using valuate_update_x[of "rhs e" x "\<langle>v\<rangle>" "\<langle>v\<rangle>(x := c)"]
    by (auto simp add: satisfies_eq_def)
qed (auto simp: update_code_def assert_bound'_code_def assert_bound_code_def)

global_interpretation Pivot'Default: Pivot' eq_idx_for_lvar pivot_eq subst_var 
  defines
    pivot_tableau_code = Pivot'Default.pivot_tableau and
    pivot_code = Pivot'Default.pivot
  rewrites
    "Pivot'.pivot eq_idx_for_lvar pivot_eq subst_var = pivot_code" and
    "Pivot'.pivot_tableau eq_idx_for_lvar pivot_eq subst_var = pivot_tableau_code" and
    "SubstVar.subst_var_eq subst_var = subst_var_eq_code"
  by (unfold_locales, auto simp: pivot_tableau_code_def pivot_code_def)

global_interpretation PivotUpdateDefault: PivotUpdate eq_idx_for_lvar pivot_code update_code 
  defines 
    pivot_and_update_code = PivotUpdateDefault.pivot_and_update
  rewrites
    "PivotUpdate.pivot_and_update pivot_code update_code = pivot_and_update_code"
  by (unfold_locales, auto simp: pivot_and_update_code_def)

global_interpretation PivotUpdateMinVarsDefault: PivotUpdateMinVars eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update_code 
  defines 
    check'_code = PivotUpdateMinVarsDefault.check' and
    check_code  = PivotUpdateMinVarsDefault.check
  rewrites
    "PivotUpdateMinVars.check eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update_code = check_code" and 
    "PivotUpdateMinVars.check' eq_idx_for_lvar min_rvar_incdec_eq pivot_and_update_code = check'_code"
  by (unfold_locales) (simp_all add: check_code_def check'_code_def)

global_interpretation Assert'Default: Assert' assert_bound_code check_code 
  defines 
    assert_code = Assert'Default.assert
  rewrites
    "Assert'.assert assert_bound_code check_code = assert_code"
  by (unfold_locales, auto simp: assert_code_def)

global_interpretation AssertAllStateDefault: AssertAllState'' init_state assert_bound_code check_code 
  defines 
    assert_bound_loop_code = AssertAllStateDefault.assert_bound_loop and
    assert_all_state_code = AssertAllStateDefault.assert_all_state and
    assert_all_code = AssertAllStateDefault.assert_all
  rewrites
    "AssertAllState''.assert_bound_loop assert_bound_code = assert_bound_loop_code" and
    "AssertAllState''.assert_all_state init_state assert_bound_code check_code = assert_all_state_code" and
    "AssertAllState.assert_all assert_all_state_code = assert_all_code"
  by unfold_locales (simp_all add: assert_bound_loop_code_def assert_all_state_code_def assert_all_code_def)

(* -------------------------------------------------------------------------- *)
(* Preprocess preprocess  *)
(* -------------------------------------------------------------------------- *)

primrec poly :: "'a ns_constraint \<Rightarrow> linear_poly" where
  "poly (LEQ_ns p a) = p"
| "poly (GEQ_ns p a) = p"

primrec
  monom_to_atom:: "QDelta ns_constraint \<Rightarrow> QDelta atom" where
  "monom_to_atom (LEQ_ns l r) = (if (monom_coeff l < 0) then
                                                (Geq (monom_var l) (r /R monom_coeff l))
                                            else
                                                (Leq (monom_var l) (r /R monom_coeff l)))"
| "monom_to_atom (GEQ_ns l r) = (if (monom_coeff l < 0) then
                                                (Leq (monom_var l) (r /R monom_coeff l))
                                            else
                                                (Geq (monom_var l) (r /R monom_coeff l)))"

primrec
  qdelta_constraint_to_atom:: "QDelta ns_constraint \<Rightarrow> var \<Rightarrow> QDelta atom" where
  "qdelta_constraint_to_atom (LEQ_ns l r) v = (if (is_monom l) then (monom_to_atom (LEQ_ns l r)) else (Leq v r))"
| "qdelta_constraint_to_atom (GEQ_ns l r) v = (if (is_monom l) then (monom_to_atom (GEQ_ns l r)) else (Geq v r))"

primrec
  qdelta_constraint_to_eq:: "QDelta ns_constraint \<Rightarrow> var \<Rightarrow> eq" where
  "qdelta_constraint_to_eq (LEQ_ns l r) v = (v, l)"
| "qdelta_constraint_to_eq (GEQ_ns l r) v = (v, l)"

record istate = 
  FirstFreshVariable :: var
  Tableau :: tableau
  Atoms :: "QDelta atom list"

primrec
  preprocess' :: "QDelta ns_constraint list \<Rightarrow> var \<Rightarrow> istate" where
  "preprocess' [] v = \<lparr> FirstFreshVariable = v,
                  Tableau = [],
                  Atoms = []\<rparr>"
| "preprocess' (h # t) v = (let s' = preprocess' t v;
                         v' = FirstFreshVariable s';
                         t' = Tableau s';
                         a' = Atoms s' in
                     \<lparr>FirstFreshVariable = (if (is_monom (poly h)) then
                                                v'
                                            else
                                                v' + 1),
                      Tableau = ( if (is_monom (poly h)) then
                                     t'
                                  else
                                     (qdelta_constraint_to_eq h v' # t') ),
                      Atoms = qdelta_constraint_to_atom h v' # a'\<rparr>)"

abbreviation max_var:: "QDelta ns_constraint \<Rightarrow> var" where
"max_var C \<equiv> AbstractLinearPoly.max_var (poly C)"

primrec
  start_fresh_variable :: "QDelta ns_constraint list \<Rightarrow> var" where
  "start_fresh_variable [] = 0"
| "start_fresh_variable (h#t) = max (max_var h + 1) (start_fresh_variable t)"


definition
  preprocess  :: "QDelta ns_constraint list \<Rightarrow> tableau \<times> (QDelta atom list)" where
  "preprocess l \<equiv> let start = start_fresh_variable l; is = preprocess' l start in (Tableau is, Atoms is)"

lemma lhs_qdelta_constraint_to_eq [simp]:
  "lhs (qdelta_constraint_to_eq h v) = v"
  by (cases h) auto

lemma rvars_eq_qdelta_constraint_to_eq [simp]:
  "rvars_eq (qdelta_constraint_to_eq h v) = vars (poly h)"
  by (cases h) auto

lemma fresh_var_monoinc: 
  "FirstFreshVariable (preprocess' cs start) \<ge> start"
  by (induct cs) (auto simp add: Let_def)

abbreviation vars_constraints where
 "vars_constraints cs \<equiv> \<Union> set (map vars (map poly cs))" 

lemma start_fresh_variable_fresh:
  "\<forall> var \<in> vars_constraints cs. var < start_fresh_variable cs"
  using max_var_max
  by (induct cs, auto simp add: max_def) force+
  
lemma vars_tableau_vars_constraints:
  "rvars (Tableau (preprocess' cs start)) \<subseteq> vars_constraints cs"
  by (induct cs) (auto simp add: rvars_def Let_def)

lemma lvars_tableau_ge_start:
  "\<forall> var \<in> lvars (Tableau (preprocess' cs start)). var \<ge> start"
  by (induct cs) (auto simp add: Let_def lvars_def fresh_var_monoinc)

lemma first_fresh_variable_not_in_lvars:
  "\<forall>var \<in> lvars (Tableau (preprocess' cs start)). FirstFreshVariable (preprocess' cs start) > var"
  by (induct cs) (auto simp add: Let_def lvars_def) 

lemma sat_atom_sat_eq_sat_constraint_non_monom:
  assumes "v \<Turnstile>\<^sub>a qdelta_constraint_to_atom h var" "v \<Turnstile>\<^sub>e qdelta_constraint_to_eq h var" "\<not> is_monom (poly h)"
  shows "v \<Turnstile>\<^sub>n\<^sub>s h"
  using assms
  by (cases h) (auto simp add: satisfies_eq_def split: if_splits)

lemma qdelta_constraint_to_atom_monom:
  assumes "is_monom (poly h)"
  shows "v \<Turnstile>\<^sub>a qdelta_constraint_to_atom h var \<longleftrightarrow> v \<Turnstile>\<^sub>n\<^sub>s h"
proof (cases h)
  case (LEQ_ns l a)
  thus ?thesis
    using assms
    using monom_valuate[of _ v]
    apply auto
    using scaleRat_leq2[of "a /R monom_coeff l" "v (monom_var l)" "monom_coeff l"]
    using divide_leq1[of "monom_coeff l" "v (monom_var l)" a]
    apply (force, simp add: divide_rat_def)
    using scaleRat_leq1[of "v (monom_var l)" "a /R monom_coeff l" "monom_coeff l"]
    using is_monom_monom_coeff_not_zero[of l]
    using divide_leq[of "monom_coeff l" "v (monom_var l)" a]
    using is_monom_monom_coeff_not_zero[of l]
    by (simp_all add: divide_rat_def)
next
  case (GEQ_ns l a)
  thus ?thesis
    using assms
    using monom_valuate[of _ v]
    apply auto
    using scaleRat_leq2[of "v (monom_var l)" "a /R monom_coeff l" "monom_coeff l"]
    using divide_geq1[of a "monom_coeff l" "v (monom_var l)"]
    apply (force, simp add: divide_rat_def)
    using scaleRat_leq1[of "a /R monom_coeff l" "v (monom_var l)" "monom_coeff l"]
    using is_monom_monom_coeff_not_zero[of l]
    using divide_geq[of a "monom_coeff l" "v (monom_var l)"]
    using is_monom_monom_coeff_not_zero[of l]
    by (simp_all add: divide_rat_def)
qed

lemma preprocess'_sat:
  assumes "v \<Turnstile>\<^sub>a\<^sub>s set (Atoms (preprocess' s start))" "v \<Turnstile>\<^sub>t Tableau (preprocess' s start)"
  shows "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s s"
  using assms
  by (induct s) (auto simp add: Let_def satisfies_atom_set_def satisfies_tableau_def qdelta_constraint_to_atom_monom sat_atom_sat_eq_sat_constraint_non_monom
                      split: if_splits)

lemma sat_constraint_valuation:
  assumes "\<forall> var \<in> vars (poly c). v1 var = v2 var"
  shows "v1 \<Turnstile>\<^sub>n\<^sub>s c \<longleftrightarrow> v2 \<Turnstile>\<^sub>n\<^sub>s c"
  using assms
  using valuate_depend
  by (cases c) (force)+

lemma atom_var_first:
  assumes "a \<in> set (Atoms (preprocess' cs start))" "\<forall> var \<in> vars_constraints cs. var < start"
  shows "atom_var a < FirstFreshVariable (preprocess' cs start)"
  using assms
proof(induct cs)
  case Nil
  thus ?case
    by simp
next
  case (Cons h t)
  show ?case
  proof(cases "a \<in> set (Atoms (preprocess' t start))")
    case True
    thus ?thesis
      using Cons(1) Cons(3)
      by (auto simp add: Let_def)
  next
    case False
    from Cons(3) monom_var_in_vars
    have "is_monom (poly h) \<Longrightarrow> monom_var (poly h) < start" by auto
    moreover from False have "a = qdelta_constraint_to_atom h (FirstFreshVariable (preprocess' t start))"
      using Cons(2)
      by (simp add: Let_def)
    ultimately show ?thesis      
      using fresh_var_monoinc[of start t]
      by (cases a; cases h) 
         (auto simp add: Let_def split: if_splits)
  qed
qed

lemma satisfies_tableau_satisfies_tableau:
  assumes "v1 \<Turnstile>\<^sub>t t" "\<forall> var \<in> tvars t. v1 var = v2 var"
  shows "v2 \<Turnstile>\<^sub>t t"
  using assms
  using valuate_depend[of _ v1 v2]
  by (force simp add: lvars_def rvars_def satisfies_eq_def satisfies_tableau_def)

lemma preprocess'_unsat:
  assumes "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s s" "vars_constraints s \<subseteq> V" "\<forall>var \<in> V. var < start"
  shows "\<exists>v'. (\<forall>var \<in> V. v var = v' var) \<and> v' \<Turnstile>\<^sub>a\<^sub>s set (Atoms (preprocess' s start)) \<and> v' \<Turnstile>\<^sub>t Tableau (preprocess' s start)"
  using assms
proof(induct s)
  case Nil
  show ?case
    by (auto simp add: satisfies_atom_set_def satisfies_tableau_def)
next
  case (Cons h t)
  then obtain v' where
    "(\<forall>var\<in>V. v var = v' var)" "v' \<Turnstile>\<^sub>a\<^sub>s set (Atoms (preprocess' t start))" "v' \<Turnstile>\<^sub>t Tableau (preprocess' t start)"
    by auto
  show ?case
  proof(cases "is_monom (poly h)")
    case True
    thus ?thesis
      using Cons
      apply (auto simp add: Let_def qdelta_constraint_to_atom_monom satisfies_atom_set_def satisfies_tableau_def)
      apply (rule_tac x=v' in exI)
      apply (subst sat_constraint_valuation[of _ _ v])
      apply auto
      done
  next
    case False
    let ?x = "FirstFreshVariable (preprocess' t start)"
    let ?y = "poly h \<lbrace> v'\<rbrace>"
    let ?v' = "v'(?x:=?y)"
    have "(\<forall>var\<in>V. v var = ?v' var)"
      using `(\<forall>var\<in>V. v var = v' var)`
      using fresh_var_monoinc[of start t]
      using Cons(4)
      by auto
    moreover
    have "?v' \<Turnstile>\<^sub>a qdelta_constraint_to_atom h (FirstFreshVariable (preprocess' t start))"
    proof-
      have "\<forall> var \<in> vars (poly h). v var = v' var"
        using `(\<forall>var\<in>V. v var = v' var)` Cons(3)
        by auto
      hence "v \<Turnstile>\<^sub>n\<^sub>s h \<longleftrightarrow> v' \<Turnstile>\<^sub>n\<^sub>s h"
        by (rule sat_constraint_valuation) 
      thus ?thesis
        using False
        using Cons(2)
        by (cases h) auto
    qed
    moreover
    have "?v' \<Turnstile>\<^sub>a\<^sub>s set (Atoms (preprocess' t start))"
      unfolding satisfies_atom_set_def
    proof
      fix a
      assume "a \<in> set (Atoms (preprocess' t start))"
      hence "v' \<Turnstile>\<^sub>a a"
        using `v' \<Turnstile>\<^sub>a\<^sub>s set (Atoms (preprocess' t start))`
        by (simp add: satisfies_atom_set_def)
      thus "?v' \<Turnstile>\<^sub>a a"
        using `a \<in> set (Atoms (preprocess' t start))`
        using atom_var_first[of a t start]
        using Cons(3) Cons(4)
        by (cases a) auto 
    qed
    moreover
    have "?v' \<Turnstile>\<^sub>e qdelta_constraint_to_eq h (FirstFreshVariable (preprocess' t start))"
      using Cons(3) Cons(4)
      using valuate_depend[of "poly h" v' "v'(FirstFreshVariable (preprocess' t start) := (poly h) \<lbrace> v' \<rbrace>)"]
      using fresh_var_monoinc[of start t]
      by (cases h) (force simp add: satisfies_eq_def)+
    moreover
    have "FirstFreshVariable (preprocess' t start) \<notin> tvars (Tableau (preprocess' t start))"
      using first_fresh_variable_not_in_lvars[of t start]
      using Cons(3) Cons(4)
      using vars_tableau_vars_constraints[of t start]
      using fresh_var_monoinc[of start t]
      by force
    hence "?v' \<Turnstile>\<^sub>t Tableau (preprocess' t start)"
      using `v' \<Turnstile>\<^sub>t Tableau (preprocess' t start)`
      using satisfies_tableau_satisfies_tableau[of v' "Tableau (preprocess' t start)" ?v']
      by auto
    ultimately
    show ?thesis
      using False
      by (rule_tac x="?v'" in exI) (auto simp add: satisfies_atom_set_def satisfies_tableau_def Let_def fun_upd_def)
  qed
qed

lemma lvars_distinct:
  "distinct (map lhs (Tableau (preprocess' cs start)))"
  using first_fresh_variable_not_in_lvars
  by (induct cs, auto simp add: Let_def lvars_def) force

interpretation PreprocessDefault: Preprocess preprocess
proof
  fix cs
  show "let (t, as) = preprocess cs in \<triangle> t"
    using lvars_distinct
    using lvars_tableau_ge_start[of cs "start_fresh_variable cs"]
    using vars_tableau_vars_constraints[of cs "start_fresh_variable cs"]
    using start_fresh_variable_fresh[of cs]
    by (force simp add: Let_def normalized_tableau_def preprocess_def)
next
  fix cs v
  show "let (t, as) = preprocess cs in v \<Turnstile>\<^sub>a\<^sub>s set as \<and> v \<Turnstile>\<^sub>t t \<longrightarrow> v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s  cs"
    by (auto simp add: preprocess'_sat preprocess_def Let_def)
next
  fix cs::"QDelta ns_constraint list" and v
  show "let (t, as) = preprocess cs in v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s  cs \<longrightarrow> (\<exists>v'. v' \<Turnstile>\<^sub>a\<^sub>s set as \<and> v' \<Turnstile>\<^sub>t t)"
    unfolding preprocess_def
    using preprocess'_unsat[of cs v "vars_constraints cs" "start_fresh_variable cs"]
    by (auto simp add: Let_def start_fresh_variable_fresh)
qed

global_interpretation Solve_exec_ns'Default: Solve_exec_ns' preprocess assert_all_code 
  defines solve_exec_ns_code = Solve_exec_ns'Default.solve_exec_ns
  by unfold_locales

(* -------------------------------------------------------------------------- *)
(* To_ns to_ns from_ns  *)
(* -------------------------------------------------------------------------- *)

primrec
  constraint_to_qdelta_constraint:: "constraint \<Rightarrow> QDelta ns_constraint list" where
  "constraint_to_qdelta_constraint (LT l r) = [LEQ_ns l (QDelta.QDelta r (-1))]" 
| "constraint_to_qdelta_constraint (GT l r) = [GEQ_ns l (QDelta.QDelta r 1)]"
| "constraint_to_qdelta_constraint (LEQ l r) = [LEQ_ns l (QDelta.QDelta r 0)]"
| "constraint_to_qdelta_constraint (GEQ l r) = [GEQ_ns l (QDelta.QDelta r 0)]"
| "constraint_to_qdelta_constraint (EQ l r) = [LEQ_ns l (QDelta.QDelta r 0), GEQ_ns l (QDelta.QDelta r 0)]"
| "constraint_to_qdelta_constraint (LTPP l1 l2) = [LEQ_ns (l1 - l2) (QDelta.QDelta 0 (-1))]"
| "constraint_to_qdelta_constraint (GTPP l1 l2) = [GEQ_ns (l1 - l2) (QDelta.QDelta 0 1)]"
| "constraint_to_qdelta_constraint (LEQPP l1 l2) = [LEQ_ns (l1 - l2) 0]"
| "constraint_to_qdelta_constraint (GEQPP l1 l2) = [GEQ_ns (l1 - l2) 0]"
| "constraint_to_qdelta_constraint (EQPP l1 l2) = [LEQ_ns (l1 - l2) 0, GEQ_ns (l1 - l2) 0]" 

definition
  to_ns :: "constraint list \<Rightarrow> QDelta ns_constraint list" where
  "to_ns l \<equiv> concat (map constraint_to_qdelta_constraint l)"

primrec
  \<delta>0_val :: "QDelta ns_constraint \<Rightarrow> QDelta valuation \<Rightarrow> rat" where
  "\<delta>0_val (LEQ_ns lll rrr) vl = \<delta>0 lll\<lbrace>vl\<rbrace> rrr"
| "\<delta>0_val (GEQ_ns lll rrr) vl = \<delta>0 rrr lll\<lbrace>vl\<rbrace>"

primrec
  \<delta>0_val_min :: "QDelta ns_constraint list \<Rightarrow> QDelta valuation \<Rightarrow> rat" where
  "\<delta>0_val_min [] vl = 1"
| "\<delta>0_val_min (h#t) vl = min (\<delta>0_val_min t vl) (\<delta>0_val h vl)"

abbreviation vars_list_constraints where
  "vars_list_constraints cs \<equiv> remdups (concat (map AbstractLinearPoly.vars_list (map poly cs)))"

definition
  from_ns ::"(var, QDelta) mapping \<Rightarrow> QDelta ns_constraint list \<Rightarrow> (var, rat) mapping" where
  "from_ns vl cs \<equiv> let \<delta> = \<delta>0_val_min cs \<langle>vl\<rangle> in 
      Mapping.tabulate (vars_list_constraints cs) (\<lambda> var. val (\<langle>vl\<rangle> var) \<delta>)"


global_interpretation SolveExec'Default: SolveExec' to_ns from_ns solve_exec_ns_code 
  defines solve_exec_code = SolveExec'Default.solve_exec
  and solve_code = SolveExec'Default.solve
proof (unfold_locales)
  fix cs v'
  assume "\<langle>v'\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s to_ns cs"
  show "\<langle>from_ns v' (to_ns cs)\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs"
  proof
    fix c
    let ?list = "map (\<lambda>C. case C of (LEQ_ns l r) \<Rightarrow> (l\<lbrace>\<langle>v'\<rangle>\<rbrace>, r)
                                  | (GEQ_ns l r) \<Rightarrow> (r, l\<lbrace>\<langle>v'\<rangle>\<rbrace>)
                     ) (to_ns cs)"
    have "\<And> qd1 qd2. (qd1, qd2) \<in> set ?list \<Longrightarrow> qd1 \<le> qd2"
    proof-
      fix qd1 qd2
      assume "(qd1, qd2) \<in> set ?list"
      thus "qd1 \<le> qd2"
        using `\<langle>v'\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s to_ns cs`
      proof(induct cs)
        case Nil
        thus ?case
          by (simp add: to_ns_def)
      next
        case (Cons h t)
        thus ?case
          by (induct h) (auto simp add: to_ns_def)
      qed
    qed
    hence l1: "\<forall>qd1 qd2. (qd1, qd2) \<in> set ?list \<longrightarrow> val qd1 (\<delta>_min ?list) \<le> val qd2 (\<delta>_min ?list)"
      by (simp add: delta_gt_zero delta_min[of ?list])
    have "\<delta>0_val_min (to_ns cs) \<langle>v'\<rangle> = \<delta>_min ?list"
    proof(induct cs)
      case Nil
      show ?case
        by (simp add: to_ns_def)
    next
      case (Cons h t)
      thus ?case
        by (cases h) (auto simp add: to_ns_def)
    qed
    hence l2: "from_ns v' (to_ns cs) = Mapping.tabulate (vars_list_constraints (to_ns cs)) (\<lambda> var. val (\<langle>v'\<rangle> var) (\<delta>_min ?list))"
      by (auto simp add: from_ns_def)
    assume "c \<in> set cs"
    thus "\<langle>from_ns v' (to_ns cs)\<rangle> \<Turnstile>\<^sub>c c"
    proof (induct c)
      case (LT lll rrr)
      hence "(lll\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta rrr (-1))) \<in> set ?list"
        by (force simp add: to_ns_def)
      hence "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<le> val (QDelta.QDelta rrr (-1)) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars lll"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `LT lll rrr \<in> set cs`
          by (auto simp add: comp_def lookup_tabulate restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<le> (val (QDelta.QDelta rrr (-1)) (\<delta>_min ?list))"
        by (auto simp add: valuate_rat_valuate)
      thus ?case
        using delta_gt_zero[of "?list"]
        by (simp add: val_def)
    next
      case (GT lll rrr)
      hence "((QDelta.QDelta rrr 1), lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list"
        by (force simp add: to_ns_def)
      hence "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<ge> val (QDelta.QDelta rrr 1) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars lll"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `GT lll rrr \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<ge> val (QDelta.QDelta rrr 1) (\<delta>_min ?list)"
        using l2
        by (simp add: valuate_rat_valuate)
      thus ?case
        using delta_gt_zero[of "?list"]
        by (simp add: val_def)
    next
      case (LEQ lll rrr)
      hence "(lll\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta rrr 0) ) \<in> set ?list"
        by (force simp add: to_ns_def)
      hence "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<le> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars lll"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `LEQ lll rrr \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<le> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)"
        using l2
        by (simp add: valuate_rat_valuate)
      thus ?case
        by (simp add: val_def)
    next
      case (GEQ lll rrr)
      hence "((QDelta.QDelta rrr 0), lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list"
        by (force simp add: to_ns_def)
      hence "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars lll"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `GEQ lll rrr \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)"
        using l2
        by (simp add: valuate_rat_valuate)
      thus ?case
        by (simp add: val_def)
    next
      case (EQ lll rrr)
      hence "((QDelta.QDelta rrr 0), lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" and
            "(lll\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta rrr 0) ) \<in> set ?list"
        by (force simp add: to_ns_def)+
      hence "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)" and
            "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<le> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)"
        using l1
        by simp_all
      moreover
      have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars lll"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `EQ lll rrr \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)" and
           "lll\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<le> val (QDelta.QDelta rrr 0) (\<delta>_min ?list)"
        using l1
        by (auto simp add: valuate_rat_valuate)
      thus ?case
        by (simp add: val_def)
    next
      case (LTPP ll1 ll2)
      hence "((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta 0 (-1)) ) \<in> set ?list"
        by (force simp add: to_ns_def)
      hence "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<le> val (QDelta.QDelta 0 (-1)) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            (ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars (ll1 - ll2)"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `LTPP ll1 ll2  \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "(ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<le> val (QDelta.QDelta 0 (-1)) (\<delta>_min ?list)"
        using l1
        by (simp add: valuate_rat_valuate)
      thus ?case
        using delta_gt_zero[of "?list"]
        by (simp add: val_def valuate_minus)
    next
      case (GTPP ll1 ll2)
      hence "((QDelta.QDelta 0 1), (ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list"
        by (force simp add: to_ns_def)
      hence "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<ge> val (QDelta.QDelta 0 1) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            (ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars (ll1 - ll2)"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `GTPP ll1 ll2  \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "(ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<ge> val (QDelta.QDelta 0 1) (\<delta>_min ?list)"
        using l1
        by (simp add: valuate_rat_valuate)
      thus ?case
        using delta_gt_zero[of "?list"]
        by (simp add: val_def valuate_minus)
    next
      case (LEQPP ll1 ll2)
      hence "((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta 0 0) ) \<in> set ?list"
        by (force simp add: to_ns_def zero_QDelta_def)
      hence "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<le> val (QDelta.QDelta 0 0) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            (ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars (ll1 - ll2)"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `LEQPP ll1 ll2  \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "(ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<le> val (QDelta.QDelta 0 0) (\<delta>_min ?list)"
        using l1
        by (simp add: valuate_rat_valuate)
      thus ?case
        using delta_gt_zero[of "?list"]
        by (simp add: val_def valuate_minus)
    next
      case (GEQPP ll1 ll2)
      hence "((QDelta.QDelta 0 0), (ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list"
        by (force simp add: to_ns_def zero_QDelta_def)
      hence "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<ge> val (QDelta.QDelta 0 0) (\<delta>_min ?list)"
        using l1
        by simp
      moreover
      have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            (ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars (ll1 - ll2)"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `GEQPP ll1 ll2  \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "(ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<ge> val (QDelta.QDelta 0 0) (\<delta>_min ?list)"
        using l1
        by (simp add: valuate_rat_valuate)
      thus ?case
        using delta_gt_zero[of "?list"]
        by (simp add: val_def valuate_minus)
    next
      case (EQPP ll1 ll2)
      hence "((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta 0 0) ) \<in> set ?list" and
            "((QDelta.QDelta 0 0), (ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list"
        by (force simp add: to_ns_def zero_QDelta_def)+
      hence "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<ge> val (QDelta.QDelta 0 0) (\<delta>_min ?list)" and
            "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min ?list) \<le> val (QDelta.QDelta 0 0) (\<delta>_min ?list)"
        using l1
        by simp_all
      moreover
      have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min ?list))\<rbrace> = 
            (ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace>"
      proof (rule valuate_depend, rule)
        fix x
        assume "x \<in> vars (ll1 - ll2)"
        thus "val (\<langle>v'\<rangle> x) (\<delta>_min ?list) = \<langle>from_ns v' (to_ns cs)\<rangle> x"
          using l2
          using `EQPP ll1 ll2 \<in> set cs`
          by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
      qed
      ultimately
      have "(ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<ge> val (QDelta.QDelta 0 0) (\<delta>_min ?list)" and
           "(ll1-ll2)\<lbrace>\<langle>from_ns v' (to_ns cs)\<rangle>\<rbrace> \<le> val (QDelta.QDelta 0 0) (\<delta>_min ?list)"
        using l1
        by (auto simp add: valuate_rat_valuate)
      thus ?case
        by (simp add: val_def valuate_minus)
    qed
  qed
next
  fix cs v
  assume "v \<Turnstile>\<^sub>c\<^sub>s cs"
  let ?v = "\<lambda>var. QDelta.QDelta (v var) 0"
  have "?v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s  to_ns cs"
    using `v \<Turnstile>\<^sub>c\<^sub>s cs`
  proof(induct cs)
    case Nil
    show ?case
      by (simp add: to_ns_def)
  next
    case (Cons h t)
    thus ?case
      by (cases h) (auto simp add: less_eq_QDelta_def to_ns_def valuate_valuate_rat valuate_minus zero_QDelta_def)
  qed
  thus "\<exists>v'. v' \<Turnstile>\<^sub>n\<^sub>s\<^sub>s  to_ns cs"
    by auto
qed

(* -------------------------------------------------------------------------- *)
(* Main soundness lemma and executability *)
(* -------------------------------------------------------------------------- *)

definition simplex where "simplex cs = snd (solve_exec_code cs)"

lemma simplex: "simplex cs = Some v \<Longrightarrow>  \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs" 
  "simplex cs = None \<Longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s cs)" 
proof -
  obtain b vo where exec: "solve_exec_code cs = (b,vo)" by force
  from SolveExec'Default.simplex_sat0[of cs, unfolded exec split Let_def]
  have sat: "b \<longrightarrow> \<langle>the vo\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs" .
  from SolveExec'Default.simplex_unsat0[of cs, unfolded exec split Let_def]
  have unsat: "\<not> b \<longrightarrow> (\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s cs)" .
  obtain c d where cc: "solve_exec_ns_code (to_ns cs) = (c,d)" by force
  from exec[unfolded SolveExec'Default.solve_exec_def Let_def cc split] have id: "b \<longleftrightarrow> vo \<noteq> None" 
    by (cases c, auto)
  from exec have simp: "simplex cs = vo" unfolding simplex_def by auto
  show "simplex cs = Some v \<Longrightarrow>  \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s cs" unfolding simp using id sat by auto
  show "simplex cs = None \<Longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s cs)" unfolding simp using id unsat by auto
qed

(* cleanup *)
  
hide_const (open) le lt LE LB UB inv zero Var add
  
(* New part: creating linear polynomials: via 0, +, -, ..., and lp_monom (c * x) *)
lift_definition lp_monom :: "rat \<Rightarrow> var \<Rightarrow> linear_poly" is
  "\<lambda> c x y. if x = y then c else 0" by auto

lemma valuate_lp_monom: "((lp_monom c x) \<lbrace>v\<rbrace>) = c * (v x)" 
proof (transfer, simp, goal_cases) 
  case (1 c x v)
  have id: "{v. x = v \<and> (x = v \<longrightarrow> c \<noteq> 0)} = (if c = 0 then {} else {x})" by auto
  show ?case unfolding id
    by (cases "c = 0", auto)
qed
    
lemma linear_poly_map_code[code]: "linear_poly_map (lp_monom c x) = (if c = 0 then fmempty else fmupd x c fmempty)" 
proof (rule fmap_ext, goal_cases)
  case (1 y)
  include fmap.lifting
  show ?case by (cases "c = 0", (transfer, auto)+)
qed

definition rat_of_int_pair :: "integer \<Rightarrow> integer \<Rightarrow> rat" where
  "rat_of_int_pair n d = of_int (int_of_integer n) / of_int (int_of_integer d)" 

value (code) "simplex [LTPP (lp_monom 2 1) (lp_monom 3 2 - lp_monom 3 0), GT (lp_monom 1 1) 5]"

export_code simplex lp_monom LTPP rat_of_int_pair nat_of_integer in OCaml module_name Simplex file "~/tmp/tmp/Simplex.ml" 
end