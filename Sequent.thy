
section \<open>Sequent Calculus\<close>

theory Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Multiset"
begin

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and formulae are defined as follows:
\<close>
type_synonym var_sym = string
type_synonym fun_sym = string
type_synonym pred_sym = string
type_synonym var_denot = \<open>nat \<Rightarrow> var_sym\<close>
type_synonym 'u fun_denot = \<open>fun_sym \<Rightarrow> 'u list \<Rightarrow> 'u\<close>
type_synonym 'u pred_denot = \<open>pred_sym \<Rightarrow> 'u list \<Rightarrow> bool\<close>

datatype (params_tm: 'f) tm  = Var nat | Fun 'f \<open>nat list\<close>

primrec semantics_tm :: "(nat \<Rightarrow> string) \<Rightarrow> ('f \<Rightarrow> string list \<Rightarrow> string) \<Rightarrow> 'f tm \<Rightarrow> string" (\<open>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<lparr>E, F\<rparr> (Var n) = E n\<close>
| \<open>\<lparr>E, F\<rparr> (Fun f ts) = F f (map E ts)\<close>

datatype 'f form = 
    EqAtom "'f tm" "'f tm"
  | NEqAtom "'f tm" "'f tm"
  | ConcEq "'f tm" "'f tm" "'f tm"
  | Member "'f tm" "char BA rexp"
  | NMember "'f tm" "char BA rexp"
  | Dis "'f form" "'f form"                     
  | Con "'f form" "'f form"                      
  | Neg "'f form"     
  | FF


primrec semantics_fm (\<open>\<lbrakk>_, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>E, F\<rbrakk> (EqAtom x y) = (\<lparr>E, F\<rparr> x = \<lparr>E, F\<rparr> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (NEqAtom x y) = (\<lparr>E, F\<rparr> x \<noteq> \<lparr>E, F\<rparr> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (ConcEq z x y) = (\<lparr>E, F\<rparr> z = \<lparr>E, F\<rparr> x @ \<lparr>E, F\<rparr> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Member x r) = (\<lparr>E, F\<rparr> x \<in> lang r)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (NMember x r) = (\<lparr>E, F\<rparr> x \<notin> lang r)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Dis x y) = (\<lbrakk>E, F\<rbrakk> x \<or> \<lbrakk>E, F\<rbrakk> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Con x y) = (\<lbrakk>E, F\<rbrakk> x \<and> \<lbrakk>E, F\<rbrakk> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Neg x) = (\<not> \<lbrakk>E, F\<rbrakk> x)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (FF) = False\<close> 

definition model :: \<open>(nat \<Rightarrow> char list) \<Rightarrow> ('f \<Rightarrow> char list list \<Rightarrow> char list) \<Rightarrow> 'f form list \<Rightarrow> 'f form \<Rightarrow> bool\<close> ("_,_,_ \<Turnstile> _" [50,50] 50) where
  \<open>(E,F,ps \<Turnstile> p) = (list_all \<lbrakk>E,F\<rbrakk> ps \<longrightarrow> \<lbrakk>E, F\<rbrakk> p)\<close>

fun pre_image_conc ::"char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where 
  "pre_image_conc r = {(a,b)| a b. lang r = (lang (Times a b))}"

fun empty_intersection_set :: "char BA rexp list \<Rightarrow> bool" where
  "empty_intersection_set fs = (\<Inter>(lang ` set fs) = {} \<and> length fs > 1 )"

fun subset_intersect_set :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "subset_intersect_set r fs = (\<Inter>(lang ` set fs) \<subseteq> lang r)"

fun eq_len_intersect :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "eq_len_intersect r fs = (\<Inter>(lang ` set fs) = lang r \<and> length fs > 1)"

fun member_var_rexp :: "nat list \<Rightarrow> char BA rexp list \<Rightarrow> string form list" where 
"member_var_rexp [] b = []"|
"member_var_rexp (v # va) [] = []"|
"member_var_rexp (x#xs) (y#ys) = (if (length xs = length ys) then (Member (Var x) y) # (member_var_rexp xs ys) else [])"

fun con_fwd_prop ::"string \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where
"con_fwd_prop f r es = (if f = ''concat'' then lang (r) = List.foldl (*) (lang (hd es)) (map lang (tl es)) else False)"

fun con_fwd_prop_elim ::"string \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where
"con_fwd_prop_elim f r es = (if f = ''concat'' then lang (r) = List.foldl (*) (lang (hd es)) (map lang (tl es)) \<and> is_singleton (lang r) else False)"

fun con_bwd_prop ::"string \<Rightarrow> char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
"con_bwd_prop f r = (if f = ''concat'' then pre_image_conc r else {})"

inductive One_SC :: \<open>string form list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> 0) where
  AlphaCon:      \<open>\<turnstile> A#B#\<Gamma> \<Longrightarrow> \<turnstile> Con A B#\<Gamma>\<close>
| AlphaNegOr:    \<open>\<turnstile> Neg A #Neg B#\<Gamma> \<Longrightarrow> \<turnstile> Neg (Dis A B)# \<Gamma>\<close>
| AlphaOr:       \<open>\<turnstile> A# \<Gamma> \<Longrightarrow> \<turnstile> B # \<Gamma> \<Longrightarrow> \<turnstile> Dis A B # \<Gamma>\<close>
| AlphaNegAnd:   \<open>\<turnstile> Neg A # \<Gamma> \<Longrightarrow>  \<turnstile> Neg B # \<Gamma> \<Longrightarrow> \<turnstile> Neg (Con A B) # \<Gamma>\<close>
| AlphaNegNeg:   \<open>\<turnstile> A# \<Gamma> \<Longrightarrow> \<turnstile> Neg (Neg A) # \<Gamma>\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> (Member x ec) # \<Gamma> \<Longrightarrow> \<turnstile> (NMember x e) # \<Gamma>\<close>
| NotEq:         \<open>\<turnstile> EqAtom x y # (EqAtom y (Fun f fs) # \<Gamma>) \<Longrightarrow> \<turnstile> EqAtom x (Fun f fs)# \<Gamma>\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> Member x e # \<Gamma> \<Longrightarrow> \<turnstile> Member x ec # \<Gamma> \<Longrightarrow>  \<turnstile> \<Gamma>\<close>
| EqProp:        \<open>\<turnstile> Member x e # EqAtom x y # Member y e # \<Gamma> \<Longrightarrow> \<turnstile> Member x e # EqAtom x y # \<Gamma>\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<turnstile> Member x e1 # Member y e2 # \<Gamma> \<Longrightarrow> \<turnstile> Member x e1 # NEqAtom x y # Member y e2 # \<Gamma>\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<turnstile> Member x e # Member y e # \<Gamma>\<Longrightarrow> \<turnstile> Member x e # (EqAtom x y) # \<Gamma>\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<turnstile> (Member x e) # (Member y ec) # \<Gamma> \<Longrightarrow>  
                 \<turnstile> (Member x e) # (NEqAtom x y) # \<Gamma>\<close>
| Close:         \<open>empty_intersection_set fs \<Longrightarrow> \<turnstile> [FF] \<Longrightarrow> \<turnstile> ((map (\<lambda>r. Member x r) fs)) @ \<Gamma>\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<turnstile> (map (\<lambda>r. Member x r) fs) @ \<Gamma> \<Longrightarrow> \<turnstile> Member x e # (map (\<lambda>r. Member x r) fs) @ \<Gamma>\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<turnstile> Member x e # \<Gamma>  \<Longrightarrow>  \<turnstile> (map (\<lambda>r. Member x r) (fs)) @ \<Gamma>\<close> 
| Order:         \<open>\<turnstile> G \<Longrightarrow> set G = set G' \<Longrightarrow> \<turnstile> G'\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop f e es \<Longrightarrow> \<turnstile> (Member x e)#(EqAtom x (Fun f xs))#(member_var_rexp xs es) @ \<Gamma> 
                 \<Longrightarrow> \<turnstile> (EqAtom x (Fun f xs))#(member_var_rexp xs es) @ \<Gamma>\<close>  
| Fwd_ElimConc:  \<open>con_fwd_prop_elim f e es \<Longrightarrow> \<turnstile> Member x e # EqAtom x (Fun f xs)# member_var_rexp xs es  @ \<Gamma> \<Longrightarrow>  
                 \<turnstile> (EqAtom x (Fun f xs)# member_var_rexp xs es) @ \<Gamma>\<close>(*
| Bwd_PropConc:  \<open>con_bwd_prop f e = es \<Longrightarrow> \<turnstile> ((\<lambda>r. Member (Var (hd xs)) (fst r)# Member (Var (hd (tl xs))) (snd r)# Member x e # EqAtom x (Fun f xs) # \<Gamma>) ` es) \<Longrightarrow> 
                 \<turnstile> Member x e # EqAtom x (Fun f xs)# \<Gamma>\<close>*)


lemma "False \<or> True \<Longrightarrow> True"
  apply (erule disjE)
   apply simp
  apply simp
  done

subsection \<open>Soundness\<close>

lemma SC_soundness: \<open>\<turnstile> \<Gamma> \<Longrightarrow> \<forall>p\<in> set \<Gamma>. \<lbrakk>E, F\<rbrakk> p\<close>
proof (induct \<Gamma> rule: One_SC.induct)
  case (AlphaCon A B \<Gamma>)
  then show ?case by auto
next
  case (AlphaNegOr A B \<Gamma>)
  then show ?case by auto
next
  case (AlphaOr A \<Gamma> B)
  then show ?case by auto
next
  case (AlphaNegAnd A \<Gamma> B)
  then show ?case by auto
next
  case (AlphaNegNeg A \<Gamma>)
  then show ?case by auto
next
  case (NotMember e ec x \<Gamma>)
  then show ?case by auto
next
  case (NotEq x y fs \<Gamma>)
  then show ?case by auto
next
  case (Cut e ec x \<Gamma>)
  then show ?case by auto
next
  case (EqProp x e y \<Gamma>)
  then show ?case by auto
next
  case (NeqSubsume e1 e2 x y \<Gamma>)
  then show ?case by auto
next
  case (EqPropElim e x y \<Gamma>)
  then show ?case apply simp 
    by (metis is_singletonE singletonD)
next
  case (NeqPropElim e ec x y \<Gamma> )
  then show ?case by auto
next
  case (Close fs x \<Gamma>)
  then show ?case by simp
next
  case (Subsume e fs x \<Gamma>)
  then show ?case apply auto
    by (metis (no_types, opaque_lifting) INT_iff Un_iff image_eqI in_mono semantics_fm.simps(4))
next
  case (Intersect e fs x \<Gamma>)
  then show ?case apply auto 
    by blast
next 
  case (Fwd_PropConc fa ea es x xs \<Gamma>)
  then show ?case by auto
next 
  case (Order G G')
  then show ?case by auto
next
  case (Fwd_ElimConc fa ea es x xs \<Gamma>)
  then show ?case by auto
next 
  case (Bwd_PropConc x ea fa xs \<Gamma>)
  then show ?case  by auto
qed
 

subsection \<open>Completeness\<close>

theorem SC_completeness:
  assumes \<open>\<forall>p\<in> set G. eval e f p\<close>
  shows \<open>\<turnstile> G\<close>
  sorry

end