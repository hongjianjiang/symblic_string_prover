
section \<open>Sequent Calculus\<close>

theory Sequent imports Symbolic_Regular_Algebra_Model begin

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and formulae are defined as follows:
\<close>

datatype ('a, 'b, 'c) form = 
    Eq 'a 'a
  | Concat 'a 'a 'a
  | Extract 'a nat 'b 'a
  | Replace 'a 'b 'c 'a
  | ReplaceAll 'a 'b 'c 'a
  | Member 'a \<open>('a) rexp\<close>
  | Dis \<open>('a, 'b, 'c) form\<close> \<open>('a, 'b, 'c) form\<close>
  | Con \<open>('a, 'b, 'c) form\<close> \<open>('a, 'b, 'c) form\<close>
  | Neg \<open>('a, 'b, 'c) form\<close>


end