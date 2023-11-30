
section \<open>Sequent Calculus\<close>

theory Sequent 
  imports Symbolic_Regular_Algebra_Model 
begin

section \<open>Terms and ('a, 'b, 'c) formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and ('a, 'b, 'c) formulae are defined as follows:
\<close>

datatype 'a bterm = Var nat | App 'a "('a) bterm list" 

datatype ('a, 'b, 'c) form = 
    EqAtom "'a bterm" "'a bterm"                      
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

definition model :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c list \<Rightarrow> 'c  \<Rightarrow> bool) \<Rightarrow>
    ('c  \<Rightarrow> 'c \<Rightarrow> 'c  \<Rightarrow> bool)  \<Rightarrow>  ('a, 'b, 'c) form list \<Rightarrow> ('a, 'b, 'c) form \<Rightarrow> bool\<close> ("_,_,_,_,_ \<Turnstile> _" [50,50] 50) where
  \<open>(e,f,g,c,ps \<Turnstile> p) = (list_all (eval e f g c) ps \<longrightarrow> eval e f g c p)\<close>


fun empty_intersection_list :: "'c rexp list \<Rightarrow> bool" where 
  "empty_intersection_list fs = (List.foldl (\<inter>) (lang (hd fs)) (map lang (tl fs)) = {})"

fun subset_intersect_list :: "'c rexp \<Rightarrow> 'c rexp list \<Rightarrow> bool" where 
  "subset_intersect_list r fs = (List.foldl (\<inter>) (lang (hd fs)) (map lang (tl fs)) \<subseteq> lang r)"

fun eq_len_intersect :: "'c rexp \<Rightarrow> 'c rexp list \<Rightarrow> bool" where 
  "eq_len_intersect r fs = (List.foldl (\<inter>) (lang (hd fs)) (map lang (tl fs)) = lang r \<and> length fs > 1)"

inductive One_SC :: \<open>('a, 'b, 'c) form list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> 0) where
  AlphaCon:      \<open>\<turnstile> A # B # G \<Longrightarrow> \<turnstile> Con A B # G\<close>
| AlphaNegOr:    \<open>\<turnstile> Neg A # Neg B # G \<Longrightarrow> \<turnstile> Neg (Dis A B) # G\<close>
| AlphaOr:       \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> B # G \<Longrightarrow> \<turnstile> Dis A B # G\<close>
| AlphaNegAnd:   \<open>\<turnstile> Neg A # G \<Longrightarrow> \<turnstile> Neg B # G \<Longrightarrow> \<turnstile> Neg (Con A B) # G\<close>
| AlphaNegNeg:   \<open>\<turnstile> A # G \<Longrightarrow> \<turnstile> Neg (Neg A) # G\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> (Member x ec) # G \<Longrightarrow> \<turnstile> (Nmember x e) # G\<close>
| NEq :          \<open>\<turnstile> NeqAtom x y # (EqPred y f ts) # G \<Longrightarrow> \<turnstile> (NeqPred x f ts) # G\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> Member x e # G \<Longrightarrow> \<turnstile> Member x ec # G \<Longrightarrow>  \<turnstile> G\<close>
| EqProp:        \<open>\<turnstile> Member x e # EqAtom x y # Member y e # G \<Longrightarrow> \<turnstile> Member x e # EqAtom x y # G\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<turnstile> Member x e1 # Member y e2 # G \<Longrightarrow> \<turnstile> Member x e1 # NeqAtom x y # Member y e2 # G\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<turnstile> Member x e # Eq x y # G \<Longrightarrow> \<turnstile> Member x e # Member y e # G\<close>
| NeqPropElim:   \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> (Member x e) # (Member y e) # G \<Longrightarrow>  \<turnstile> (Member x e) # (Neq x y) # G\<close>
| Close:         \<open>empty_intersection_list fs \<Longrightarrow> \<turnstile> (map (\<lambda>r. Member x r) fs) @ G\<close>
| Subsume:       \<open>subset_intersect_list e fs \<Longrightarrow> \<turnstile> (map (\<lambda>r. Member x r) (f # fs)) @ G \<Longrightarrow> \<turnstile> Member x e # (map (\<lambda>r. Member x r) (f#fs)) @ G\<close>
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<turnstile> Member x e # G  \<Longrightarrow>  \<turnstile> (map (\<lambda>r. Member x r) (f#fs)) @ G\<close>
| Fwd_PropConc:  \<open>lang e = lang (Times e1 e2) \<Longrightarrow> \<turnstile> Member x e # EqConc x m n # Member m e1 # Member n e2 # G \<Longrightarrow> \<turnstile> EqConc x m n # Member x e1 # Member x e2 # G \<close>
| Fwd_ElimConc:  \<open>lang e = lang (Times e1 e2) \<and> is_singleton (lang e) \<Longrightarrow> is_singleton (lang e) \<Longrightarrow> \<turnstile> Member x e # Member m e1 # Member n e2 # G \<Longrightarrow>  \<turnstile> EqConc x m n # Member x e1 # Member x e2 # G\<close>
| Bwd_Prop:      \<open>lang e = lang (Times e1 e2) \<Longrightarrow> \<turnstile> Member x e # EqConc x m n # Member m e1 # Member n e2 # G \<Longrightarrow> \<turnstile> EqConc x m n # Member x e # G \<close>

lemma \<open>\<turnstile> (map (\<lambda>r. Member x r) [Atom (1::nat), Atom 2]) @ G\<close>
  apply(rule Close)
  apply auto
  done


subsection \<open>Soundness\<close>

lemma SC_soundness: \<open>\<turnstile> G \<Longrightarrow> \<exists>p \<in> set G. eval e f g c p\<close>
  apply (induct G arbitrary: f g c rule: One_SC.induct)
  subgoal for A B G f g c 
  apply simp 
    sorry
  sorry


subsection \<open>Completeness\<close>


end