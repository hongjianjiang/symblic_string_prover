
section \<open>Sequent Calculus\<close>

theory Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Multiset" Comparison_Sort_Lower_Bound.Linorder_Relations 
begin

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and formulae are defined as follows:
\<close>
datatype ('f) tm  = Var nat | Fun 'f \<open>nat list\<close>


datatype ('f) form = 
    EqAtom "'f tm" "'f tm"
  | NEqAtom "'f tm" "'f tm"
  | ConcEq "'f tm" "'f tm" "'f tm"
  | Member "'f tm" "char BA rexp"
  | NMember "'f tm" "char BA rexp"
  | Dis "'f form" "'f form"                     
  | Con "'f form" "'f form"                      
  | Neg "'f form"     
  | FF
  | TT

subsection \<open>Parameters\<close>

primrec params_tm :: "'f tm \<Rightarrow> nat set" where
  "params_tm (Var n) = {n}"|
  "params_tm (Fun f ns) = set ns"

primrec params_fm :: "'f form \<Rightarrow> nat set" where
  "params_fm (EqAtom f1 f2) = (params_tm f1 \<union> params_tm f2)"|
  "params_fm (NEqAtom f1 f2) = (params_tm f1 \<union> params_tm f2)"|
  "params_fm (ConcEq f1 f2 f3) = (params_tm f1 \<union> params_tm f2 \<union> params_tm f3)"|
  "params_fm (Member f r) = (params_tm f)"|
  "params_fm (NMember f r) = (params_tm f)"|
  "params_fm (Dis f1 f2) = (params_fm f1 \<union> params_fm f2)"|
  "params_fm (Con f1 f2) = (params_fm f1 \<union> params_fm f2)"|
  "params_fm (Neg f) = (params_fm f)"|
  "params_fm (FF) = {}"|
  "params_fm TT = {}"

abbreviation \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

subsection \<open>Semantics of term and form\<close>

primrec semantics_tm :: "(nat \<Rightarrow> string) \<Rightarrow> ('f \<Rightarrow> string list \<Rightarrow> string) \<Rightarrow> 'f tm \<Rightarrow> string" (\<open>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<lparr>E, F\<rparr> (Var n) = E n\<close>
| \<open>\<lparr>E, F\<rparr> (Fun f ts) = F f (map E ts)\<close>

fun concat_str :: "string \<Rightarrow> string list \<Rightarrow> string" where
"concat_str s ls = (if s = ''concat'' then List.concat ls else [])"

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
| \<open>\<lbrakk>E, F\<rbrakk> (TT) = True\<close> 

subsection \<open>Proof System\<close>

fun is_Member :: "'f form \<Rightarrow> bool" where 
  "is_Member (Member x r)  = True"|
  "is_Member _ = False"

fun variable_in_member :: "'f form \<Rightarrow> 'f tm option" where 
"variable_in_member (Member x r) = Some x"|
"variable_in_member _ = None"

fun rexp_in_member :: "'f form \<Rightarrow> char BA rexp  " where 
"rexp_in_member (Member x r) = r"

definition "distinct_variable  ls = distinct (map (variable_in_member) ls)"

definition "single_word ls = (List.find (\<lambda>r. \<not> is_singleton (lang r)) (map (rexp_in_member) ls) = None)"

fun exists_solution :: "string form list \<Rightarrow> bool" where
  "exists_solution ls = (if ls = [] then False 
                       else list_all is_Member ls \<and> distinct_variable ls \<and> single_word ls)"  

definition model :: \<open>(nat \<Rightarrow> char list) \<Rightarrow> ('f \<Rightarrow> char list list \<Rightarrow> char list) \<Rightarrow> 'f form list \<Rightarrow> 'f form \<Rightarrow> bool\<close> ("_,_,_ \<Turnstile> _" [50,50] 50) where
  \<open>(E,F,ps \<Turnstile> p) = (list_all \<lbrakk>E,F\<rbrakk> ps \<longrightarrow> \<lbrakk>E, F\<rbrakk> p)\<close>

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

fun con_fwd_prop ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
"con_fwd_prop r e1 r2 = (lang (r) = lang (Times e1 r2))"

fun con_fwd_prop_elim ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
"con_fwd_prop_elim r e1 e2 = (lang r = lang (Times e1 e2) \<and> is_singleton (lang r))"

fun con_bwd_prop ::" char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
"con_bwd_prop r = {(a,b)|a b. lang r = (lang (Times a b))}"

inductive One_SC :: \<open>string form list  \<Rightarrow> bool\<close> (\<open>\<stileturn> _\<close> 0) where
  AlphaCon:      \<open>\<stileturn> [A,B] @ \<Gamma> \<Longrightarrow> \<stileturn> [Con A B] @ \<Gamma>\<close>
| AlphaNegOr:    \<open>\<stileturn> Neg A #Neg B#\<Gamma> \<Longrightarrow> \<stileturn> Neg (Dis A B)# \<Gamma>\<close>
| AlphaOr:       \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> B# \<Gamma> \<Longrightarrow> \<stileturn> Dis A B # \<Gamma>\<close>
| AlphaNegAnd:   \<open>\<stileturn> Neg A # \<Gamma> \<Longrightarrow>  \<stileturn> Neg B # \<Gamma> \<Longrightarrow> \<stileturn> Neg (Con A B) # \<Gamma>\<close>
| AlphaNegNeg:   \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> Neg (Neg A) # \<Gamma>\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> (Member x ec) # \<Gamma> \<Longrightarrow> \<stileturn> (NMember x e) # \<Gamma>\<close>
| NotEq:         \<open>\<stileturn> [NEqAtom x y,  EqAtom y (Fun f xs), \<Gamma>] \<Longrightarrow> \<stileturn> [NEqAtom x (Fun f xs), \<Gamma>]\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> Member x e # \<Gamma> \<Longrightarrow>  \<stileturn> Member x ec # \<Gamma> \<Longrightarrow>  \<stileturn> \<Gamma>\<close>
| EqProp:        \<open>\<stileturn> Member x e # EqAtom x y # Member y e # \<Gamma> \<Longrightarrow> \<stileturn> Member x e # EqAtom x y # \<Gamma>\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<stileturn> Member x e1 # Member y e2 # \<Gamma> \<Longrightarrow> \<stileturn> Member x e1 # NEqAtom x y # Member y e2 # \<Gamma>\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<stileturn> Member x e # Member y e # \<Gamma>\<Longrightarrow> \<stileturn> Member x e # (EqAtom x y) # \<Gamma>\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<stileturn> (Member x e) # (Member y ec) # \<Gamma> \<Longrightarrow>  
                 \<stileturn> (Member x e) # (NEqAtom x y) # \<Gamma>\<close>
| Close:         \<open>empty_intersection_set rs \<Longrightarrow> \<stileturn> [FF] \<Longrightarrow> \<stileturn> map (\<lambda>r. Member x r) rs\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member x r) fs) @ \<Gamma> \<Longrightarrow> \<stileturn> Member x e # (map (\<lambda>r. Member x r) fs) @ \<Gamma>\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<stileturn> Member x e # \<Gamma>  \<Longrightarrow>  \<stileturn> (map (\<lambda>r. Member x r) (fs)) @ \<Gamma>\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop e e1 e2 \<Longrightarrow> \<stileturn> [(Member x e), (EqAtom x (Fun ''concat'' [x1,x2])), (Member (Var x1) e1), (Member (Var x2) e2)] @ \<Gamma>
                 \<Longrightarrow> \<stileturn> [(EqAtom x (Fun ''concat'' [x1,x2])), (Member (Var x1) e1), (Member (Var x2) e2)] @ \<Gamma>\<close>  
| Fwd_ElimConc:  \<open>con_fwd_prop_elim e e1 e2 \<Longrightarrow> \<stileturn> [Member x e, (Member (Var x1) e1), (Member (Var x2) e2)]  @ \<Gamma> \<Longrightarrow>  
                 \<stileturn> [(EqAtom x (Fun ''concat'' [x1, x2])), (Member (Var x1) e1), (Member (Var x2) e2)] @ \<Gamma>\<close>
(*| Bwd_PropConc:  \<open>con_bwd_prop e = es \<Longrightarrow> \<stileturn> ((\<lambda>r. [Member x e, EqAtom x (Fun ''concat'' [x1,x2]), Member (Var x1) (fst r), Member (Var x2) (snd r)] @ \<Gamma>) ` es) \<Longrightarrow> 
                 \<stileturn> {[Member x e, EqAtom x (Fun ''concat'' [x1,x2])] @ \<Gamma>}\<close>*)
| Order:         \<open>\<stileturn> G \<Longrightarrow> set G = set G' \<Longrightarrow> \<stileturn> G'\<close>
(*| Basic:        \<open>exists_solution G  \<Longrightarrow> \<stileturn> [FF]\<Longrightarrow> \<stileturn> G\<close>*)

declare One_SC.intros [intro]

(*lemma "\<stileturn> {((map (\<lambda>r. Member x r) [Pred (Atom CHR ''b''), Pred (Atom CHR ''a'')] @ []))}"
  apply (rule Close)
  subgoal apply auto done
  apply (rule Basic) 
  done


lemma "\<stileturn> {((map (\<lambda>r. Member x r) [Pred (Atom CHR ''b''), Pred (Atom CHR ''a'')] @ []))}"
  apply (rule Close)
  apply (auto simp:distinct_variable_def single_word_def)
  done

lemma "\<stileturn> {[Member (Var 1) (Pred (Atom CHR ''b''))]}"
  apply (rule Basic1)
  apply (auto simp:distinct_variable_def single_word_def)
  done
*)
subsection \<open>Soundness\<close>

lemma SC_soundness: \<open>\<stileturn> G \<Longrightarrow> (\<forall>p \<in> set G.  \<lbrakk>E, concat_str\<rbrakk> p)\<close>
proof (induct G rule: One_SC.induct)
  case (AlphaCon A B \<Gamma>) 
  then show ?case apply auto done
next
  case (AlphaNegOr A B \<Gamma>)
  then show ?case apply auto done
next
  case (AlphaOr A \<Gamma> B)
  then show ?case apply auto done
next
  case (AlphaNegAnd A \<Gamma> B)
  then show ?case apply auto done
next
  case (AlphaNegNeg A \<Gamma>)
  then show ?case apply auto done
next
  case (NotMember e ec x \<Gamma>)
  then show ?case apply auto done
next
  case (NotEq x y \<Gamma> z)
  then show ?case apply auto done
next
  case (Cut e ec x \<Gamma>)
  then show ?case apply auto done
next
  case (EqProp x e y \<Gamma>)
  then show ?case apply auto done
next
  case (NeqSubsume e1 e2 x y \<Gamma>)
  then show ?case apply auto done
next
  case (EqPropElim e x y \<Gamma>)
  then show ?case apply auto 
    by (metis is_singletonE singletonD)
next
  case (NeqPropElim e ec x y \<Gamma>)
  then show ?case apply (auto simp: is_singleton_def) done 
next
  case (Close rs x)
  then show ?case apply auto done
next
  case (Subsume e fs x \<Gamma>)
  then show ?case apply auto 
    by (smt (verit) INT_I Un_iff image_iff semantics_fm.simps(4) subsetD)  
next
  case (Intersect e fs x \<Gamma>)
  then show ?case  apply auto 
    by blast
next
  case (Fwd_PropConc e e1 e2 x x1 x2 \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def)  done
next
  case (Fwd_ElimConc e e1 e2 x x1 x2 \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def) 
    by (smt (verit) is_singleton_def mem_Collect_eq singleton_iff) 
(*next
  case (Bwd_PropConc e es x1 x2 x \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def) sorry*)
next
  case (Order G G')
  then show ?case apply auto done
qed

definition SC_proof :: \<open>string form list \<Rightarrow> string form \<Rightarrow> bool\<close> where
  \<open>SC_proof ps p \<equiv> (\<stileturn> p # ps)\<close>

theorem sc_soundness:
  \<open>SC_proof ps p \<Longrightarrow> list_all \<lbrakk>E, concat_str\<rbrakk> ps \<Longrightarrow> \<lbrakk>E, concat_str\<rbrakk> p\<close>
  using SC_soundness unfolding SC_proof_def list_all_def
  by fastforce

subsection \<open>Consistent sets\<close>

text \<open>
\label{sec:consistent-sets}
In this section, we describe an abstract criterion for consistent sets.
A set of sets of formulae is called a {\em consistency property}, if the
following holds:
\<close>

definition consistency :: \<open>string form set set \<Rightarrow> bool\<close> where
  \<open>consistency C = (\<forall>S. S \<in> C \<longrightarrow> FF \<notin> S \<and> 
               (\<forall>p q. \<not> (EqAtom p q \<in> S \<and> NEqAtom p q \<in> S) \<and>
               \<not> (\<forall>x r. Member x r \<in> S \<and> NMember x r \<in> S)) \<and> 
              (\<forall> A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and> 
              (\<forall> A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and> 
              (\<forall> A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and> 
              (\<forall> A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and> 
              (\<forall> A. Neg (Neg A) \<in> S \<longrightarrow> S \<union> {A} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> NMember x e \<in> S \<longrightarrow> S \<union> {Member x ec} \<in> C ) \<and> 
              (\<forall> x y f xs. NEqAtom x (Fun f xs) \<in> S \<longrightarrow> S \<union> {NEqAtom x y, EqAtom y (Fun f xs)} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> S \<union> {Member x e} \<in> C \<or> S \<union> {Member x ec} \<in> C) \<and> 
              (\<forall> x y e. Member x e \<in> S \<and> EqAtom x y \<in> S \<longrightarrow> S \<union> {Member x e, EqAtom x y, Member y e} \<in> C) \<and> 
              (\<forall> e1 e2 x y. regexp_empty e1 e2 \<longrightarrow> Member x e1 \<in> S \<and> NEqAtom x y \<in> S \<and> Member y e2 \<in> S \<longrightarrow> S \<union> {Member x e1, Member y e2} \<in> C) \<and>
              (\<forall> x y e. is_singleton (lang e) \<longrightarrow> Member x e \<in> S \<and> EqAtom x y \<in> S \<longrightarrow> S \<union> {Member x e, Member y e} \<in> C) \<and> 
              (\<forall> x y e ec. is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member x e \<in> S \<and> NEqAtom x y \<in> S \<longrightarrow> S \<union> {Member x e, Member y ec} \<in> C) \<and> 
              (\<forall> x rs. empty_intersection_set rs \<longrightarrow> S \<union> ((\<lambda>r. Member x r) ` (set rs)) \<in> C \<longrightarrow> S \<union> {FF} \<in> C) \<and> 
              (\<forall> x e fs. subset_intersect_set e fs \<longrightarrow> Member x e \<in> S \<and> S \<union> ((\<lambda>r. Member x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> ((\<lambda>r. Member x r)) ` (set fs) \<in> C) \<and> 
              (\<forall> x e fs. eq_len_intersect e fs \<longrightarrow>  S \<union> ((\<lambda>r. Member x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> {Member x e} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2 f. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom x (Fun f [x1, x2]) \<in> S \<and> Member (Var x1) e1 \<in> S \<and> Member (Var x2) e2 \<in> S \<longrightarrow> S \<union> {Member x e, EqAtom x (Fun f [x1,x2]), Member (Var x1) e1, Member (Var x2) e2} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2 f. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom x (Fun f [x1, x2]) \<in> S \<and> Member (Var x1) e1 \<in> S \<and> Member (Var x2) e2 \<in> S \<longrightarrow> S \<union> {Member x e, Member (Var x1) e1, Member (Var x2) e2} \<in> C) \<and> 
              (\<forall> S'. S' = S \<longrightarrow> S' \<in> C)) \<close>

subsection \<open>Completeness\<close>

theorem SC_completeness':
  fixes p :: \<open>string form\<close>
  assumes  mod: \<open>\<forall>e f. list_all (eval e f) ps \<longrightarrow> eval e f p\<close>
  shows \<open>SC_proof ps p\<close>
  apply(rule ccontr)
  sorry


end