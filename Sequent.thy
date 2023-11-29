
section \<open>Sequent Calculus\<close>

theory Sequent imports Symbolic_Regular_Algebra_Model begin

section \<open>Terms and ('a, 'b, 'c) formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and ('a, 'b, 'c) formulae are defined as follows:
\<close>

datatype 'a bterm = Var nat | App 'a "('a) bterm list" 

datatype ('a, 'b, 'c) form = 
    TT 
  | FF
  | EqAtom "'a bterm" "'a bterm"                      
  | EqPred "'a bterm" 'b "'a bterm list"      
  | EqConc "'a bterm" "'a bterm" "'a bterm"
  | NeqAtom "'a bterm" "'a bterm" 
  | NeqPred "'a bterm" 'b "'a bterm list"                     
  | Member "'a bterm" "'c rexp"
  | Nmember "'a bterm" "'c rexp"
  | Dis "('a, 'b, 'c) form" "('a, 'b, 'c) form"                     
  | Con "('a, 'b, 'c) form" "('a, 'b, 'c) form"                      
  | Neg "('a, 'b, 'c) form"     

primrec
  evalt :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a bterm \<Rightarrow> 'c\<close> and
  evalts :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a bterm list \<Rightarrow> 'c list\<close> where
  \<open>evalt e f (Var n) = e n\<close>
| \<open>evalt e f (App a ts) = f a (evalts e f ts)\<close>
| \<open>evalts e f [] = []\<close>
| \<open>evalts e f (t # ts) = evalt e f t # evalts e f ts\<close>


primrec eval :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow>
  ('b \<Rightarrow> 'c list \<Rightarrow> 'c \<Rightarrow> bool)  \<Rightarrow>
  ('c  \<Rightarrow> 'c \<Rightarrow> 'c  \<Rightarrow> bool)  \<Rightarrow> 
  ('a, 'b, 'c) form \<Rightarrow> bool\<close> where
  "eval e f g c (EqAtom x y) = (evalt e f x = evalt e f y)" 
| "eval e f g c (EqPred x p ts) = g p (evalts e f ts) (evalt e f x)" 
| "eval e f g c (EqConc x m n) = (c (evalt e f x) (evalt e f m) (evalt e f n))"
| "eval e f g c (NeqAtom x y) = (evalt e f x \<noteq> evalt e f y)" 
| "eval e f g c (NeqPred x p ts) = (\<not> g p (evalts e f ts) (evalt e f x))"  
| "eval e f g c (Member x r) = ([evalt e f x] \<in> lang r)"
| "eval e f g c (Nmember x r) = ([evalt e f x] \<notin> lang r)"
| "eval e f g c (Dis m n) = (eval e f g c m \<or> eval e f g c n)"
| "eval e f g c (Con m n) = (eval e f g c m \<and> eval e f g c n)"
| "eval e f g c (Neg m) = (\<not> eval e f g c m)"
| "eval e f g c (TT) = True"
| "eval e f g c (FF) = False"

inductive SC :: \<open>('a, 'b, 'c) form list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> 0) where
  AlphaNegNeg: \<open>\<turnstile> Neg (Neg A) # G \<Longrightarrow> \<turnstile> A # G \<close>
| AlphaNegOr: \<open>\<turnstile> Neg (Dis A B) # G \<Longrightarrow> \<turnstile> Neg A # Neg B # G\<close>
| AlphaCon: \<open>\<turnstile> Con A B # G \<Longrightarrow> \<turnstile> A # B # G\<close>
| BetaOr: \<open>\<turnstile> Dis A B # G \<Longrightarrow> \<turnstile> A # G \<Longrightarrow> \<turnstile> B # G\<close>
| BetaNegOr: \<open>\<turnstile> Neg (Con A B) # G \<Longrightarrow> \<turnstile> Neg A # G \<Longrightarrow> \<turnstile> Neg B # G\<close>
| NotMember: \<open>\<turnstile> Nmember x e2  # G \<Longrightarrow> lang e1 = UNIV - lang e2 \<Longrightarrow> \<turnstile> Member x e1 # G\<close>
| NEq : \<open>\<turnstile> (NeqPred x p ts) # G \<Longrightarrow> \<turnstile> NeqAtom x y # (EqPred y f ts) # G\<close>
| Cut: \<open>lang e1 = UNIV - lang e2 \<Longrightarrow> \<turnstile> G \<Longrightarrow>  \<turnstile> Member x e1 # G \<Longrightarrow> \<turnstile> Member x e2 # G\<close>
| EqPropElim: \<open>is_singleton (lang e) \<Longrightarrow> \<turnstile> Member x e # Eq x y # G \<Longrightarrow> \<turnstile> Member x e # Member y e # G\<close>
| NeqPropElim: \<open>lang e1 = UNIV - lang e2 \<Longrightarrow> \<turnstile> Member x e # Neq x y # G \<Longrightarrow> \<turnstile> Member x e1 # Member y e2 # G\<close>
| Close: \<open>List.foldl (\<inter>) (lang f) (map lang fs) = {} \<Longrightarrow> \<turnstile> (map (\<lambda>r. Member x r) (f#fs)) @ G  \<Longrightarrow> \<turnstile> [FF]\<close>
| Subsume: \<open>List.foldl (\<inter>) (lang f) (map lang fs) \<subseteq> (lang r) \<Longrightarrow> \<turnstile> Member x e # (map (\<lambda>r. Member x r) (f#fs)) @ G  \<Longrightarrow> \<turnstile> (map (\<lambda>r. Member x r) (f#fs)) @ G\<close>
| Intersect: \<open>List.foldl (\<inter>) (lang f) (map lang fs) = (lang e) \<Longrightarrow> length fs \<ge> 1 \<Longrightarrow>  \<turnstile> (map (\<lambda>r. Member x r) (f#fs)) @ G \<Longrightarrow>  \<turnstile> Member x e # G\<close>
| Fwd_Prop_Conc: \<open>lang e = lang (Times e1 e2) \<Longrightarrow> \<turnstile> EqConc x m n # Member x e1 # Member x e2 # G \<Longrightarrow> \<turnstile> Member x e # EqConc x m n # Member m e1 # Member n e2 # G\<close>
| Fwd_Elim_Conc: \<open>lang e = lang (Times e1 e2) \<Longrightarrow> is_singleton (lang e) \<Longrightarrow>  \<turnstile> EqConc x m n # Member x e1 # Member x e2 # G \<Longrightarrow> \<turnstile> Member x e # Member m e1 # Member n e2 # G\<close>
| Bwd_Prop: \<open>lang e = lang (Times e1 e2) \<Longrightarrow> \<turnstile> EqConc x m n # Member x e # G \<Longrightarrow> \<turnstile> Member x e # EqConc x m n # Member m e1 # Member n e2 # G\<close>





end