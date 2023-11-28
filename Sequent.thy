
section \<open>Sequent Calculus\<close>

theory Sequent imports Symbolic_Regular_Algebra_Model begin

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and formulae are defined as follows:
\<close>

type_synonym vname = \<open>char list\<close>
type_synonym rep = string
type_synonym crexp = "char rexp"


datatype bterm = Var nat | Conc bterm bterm

datatype form = 
    Eq vname bterm                      ("_ =:= _" [61,61] 61)
  | Neq vname bterm                     ("_ =!= _" [61,61] 61)
  | Member vname crexp
  | NMember vname crexp
  | Dis form form                      
  | Con form form                      
  | Neg form                           


primrec
  evalt :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c\<close>  where
  \<open>evalt e f (Var n) = e n\<close>
| \<open>evalt e f (App a ts) = f a (evalts e f ts)\<close>



primrec eval :: "form \<Rightarrow> bool" where
  "eval (Eq x y) = (x = y)" |
  "eval (Neg f) = (eval f)" |
  "eval (Dis f1 f2) = (eval f1 \<or> eval f2)" |
  "eval (Con f1 f2) = (eval f1 \<and> eval f2)" |
  "eval (Member x e) = (x \<in> lang e)" |
  "eval (Neq x y) = (x \<noteq> y)" |
  "eval (NMember x e) = (x \<notin> lang e)"

inductive SC :: \<open>form list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> 0) where
  AlphaNegNeg: \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> Neg (Neg A) # G\<close>
| AlphaNegOr: \<open>\<turnstile> Neg A # Neg B # G \<Longrightarrow> \<turnstile> Neg (Dis A B) # G\<close>
| AlphaCon: \<open>\<turnstile> A # B # G \<Longrightarrow> \<turnstile> Con A B # G\<close>
| BetaOr: \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> B # G \<Longrightarrow> \<turnstile> Or A B # G\<close>
| BetaNegOr: \<open>\<turnstile> Neg A # G \<Longrightarrow> \<turnstile> Neg B # G \<Longrightarrow> \<turnstile> Neg (Con A B) # G\<close>
| NotMember: \<open>lang e1 = UNIV - lang e2 \<Longrightarrow> \<turnstile> Member x e1 # G\<Longrightarrow> \<turnstile> NMember x e2  # G\<close>
| NEq : \<open>\<turnstile> Neq x y # (Func y flist) # G \<Longrightarrow> Neq x )\<close>

end