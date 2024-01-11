
section \<open>Sequent Calculus\<close>

theory Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Multiset" Comparison_Sort_Lower_Bound.Linorder_Relations 
begin

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and formulae are defined as follows:
\<close>
datatype ('f) tm  = Var nat | Fresh nat |  Fun 'f \<open>nat list\<close> 

datatype sign = pos | neg

datatype ('f) form = 
    EqAtom sign "'f tm" "'f tm"
  | EqFresh sign "'f tm" "'f tm"
  | ConcEq "'f tm" "'f tm" "'f tm"
  | Member sign "'f tm" "char BA rexp"
  | Dis "'f form" "'f form"                     
  | Con "'f form" "'f form"                      
  | Neg "'f form"     
  | FF
  | TT

subsection \<open>Fresh term\<close>

fun fresh_var :: "nat => 'f tm => bool" where
  "fresh_var x (Var y) = (x \<noteq> y)" |
  "fresh_var x (Fun f xs) = (list_all (\<lambda>a. a = x) xs)" 

primrec deX :: "'f tm => nat list" where 
  "deX (Var n) = [n] "|
  "deX (Fun f xs) = xs"

definition
  freshVar :: "string tm list => string tm" where
  "freshVar vs = Var (LEAST n. n \<notin> set (concat (map deX vs)))"

lemma "freshVar [Var (0::nat), Var 1, Var 3] = Var 2"
  apply (auto simp: freshVar_def Least_def)
  using Zero_not_Suc bot_nat_0.extremum by fastforce

subsection \<open>Semantics of term and form\<close>

primrec semantics_tm :: "(nat \<Rightarrow> string) \<Rightarrow> ('f \<Rightarrow> string list \<Rightarrow> string) \<Rightarrow> 'f tm \<Rightarrow> string" (\<open>\<lparr>_, _\<rparr>\<close>) where
  \<open>\<lparr>E, F\<rparr> (Var n) = E n\<close> |
  \<open>\<lparr>E, F\<rparr> (Fresh n) = E n\<close> |
  \<open>\<lparr>E, F\<rparr> (Fun f ts) = F f (map E ts)\<close>

fun concat_str :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "concat_str s ls = (if s = ''concat'' then List.concat ls else [])"

primrec semantics_fm (\<open>\<lbrakk>_, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>E, F\<rbrakk> (EqAtom s x y) = (if s = pos then \<lparr>E, F\<rparr> x = \<lparr>E, F\<rparr> y else \<lparr>E, F\<rparr> x \<noteq> \<lparr>E, F\<rparr> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (EqFresh s x y) = True\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (ConcEq z x y) = (\<lparr>E, F\<rparr> z = \<lparr>E, F\<rparr> x @ \<lparr>E, F\<rparr> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Member s x r) = (if s = pos then \<lparr>E, F\<rparr> x \<in> lang r else \<lparr>E, F\<rparr> x \<notin> lang r)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Dis x y) = (\<lbrakk>E, F\<rbrakk> x \<or> \<lbrakk>E, F\<rbrakk> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Con x y) = (\<lbrakk>E, F\<rbrakk> x \<and> \<lbrakk>E, F\<rbrakk> y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Neg x) = (\<not> \<lbrakk>E, F\<rbrakk> x)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (FF) = False\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (TT) = True\<close> 

subsection \<open>Proof System\<close>

fun is_Member :: "'f form \<Rightarrow> bool" where 
  "is_Member (Member s x r)  = True"|
  "is_Member _ = False"

fun variable_in_member :: "'f form \<Rightarrow> 'f tm option" where 
  "variable_in_member (Member s x r) = Some x"|
  "variable_in_member _ = None"

fun rexp_in_member :: "'f form \<Rightarrow> char BA rexp  " where 
  "rexp_in_member (Member s x r) = r"

definition "distinct_variable  ls = distinct (map (variable_in_member) ls)"

definition "single_word ls = (List.find (\<lambda>r. \<not> is_singleton (lang r)) (map (rexp_in_member) ls) = None)"

fun exists_solution :: "string form list \<Rightarrow> bool" where
  "exists_solution ls = (if ls = [] then False 
                       else list_all is_Member ls \<and> distinct_variable ls \<and> single_word ls)"  

fun empty_intersection_set :: "char BA rexp list \<Rightarrow> bool" where
  "empty_intersection_set fs = (\<Inter>(lang ` set fs) = {} \<and> length fs > 1 )"

fun subset_intersect_set :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "subset_intersect_set r fs = (\<Inter>(lang ` set fs) \<subseteq> lang r)"

fun eq_len_intersect :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "eq_len_intersect r fs = (\<Inter>(lang ` set fs) = lang r \<and> length fs > 1)"

fun member_var_rexp :: "nat list \<Rightarrow> char BA rexp list \<Rightarrow> string form list" where 
  "member_var_rexp [] b = []"|
  "member_var_rexp (v # va) [] = []"|
  "member_var_rexp (x#xs) (y#ys) = (if (length xs = length ys) then (Member pos (Var x) y) # (member_var_rexp xs ys) else [])"

fun con_fwd_prop ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop r e1 r2 = (lang (r) = lang (Times e1 r2))"

fun con_fwd_prop_elim ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop_elim r e1 e2 = (lang r = lang (Times e1 e2) \<and> is_singleton (lang r))"

fun con_bwd_prop ::" char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
  "con_bwd_prop r = {(a,b)|a b. lang r = (lang (Times a b))}"

inductive One_SC :: \<open>string form list \<Rightarrow> bool\<close> (\<open>\<stileturn> _\<close> 0) where
  AlphaCon:      \<open>\<stileturn> [A,B] @ \<Gamma> \<Longrightarrow> \<stileturn> [Con A B] @ \<Gamma>\<close>
| AlphaNegOr:    \<open>\<stileturn> Neg A #Neg B#\<Gamma> \<Longrightarrow> \<stileturn> Neg (Dis A B)# \<Gamma>\<close>
| AlphaOr:       \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> B# \<Gamma> \<Longrightarrow> \<stileturn> Dis A B # \<Gamma>\<close>
| AlphaNegAnd:   \<open>\<stileturn> Neg A # \<Gamma> \<Longrightarrow>  \<stileturn> Neg B # \<Gamma> \<Longrightarrow> \<stileturn> Neg (Con A B) # \<Gamma>\<close>
| AlphaNegNeg:   \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> Neg (Neg A) # \<Gamma>\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> (Member pos x ec) # \<Gamma> \<Longrightarrow> \<stileturn> (Member neg x e) # \<Gamma>\<close>
| NotEq:         \<open>y = freshVar ([x,(Fun f xs)])  \<Longrightarrow> \<stileturn> [EqFresh neg x y,  EqFresh pos y (Fun f xs), \<Gamma>] \<Longrightarrow> \<stileturn> [EqAtom neg x (Fun f xs), \<Gamma>]\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> Member pos x e # \<Gamma> \<Longrightarrow>  \<stileturn> Member pos x ec # \<Gamma> \<Longrightarrow>  \<stileturn> \<Gamma>\<close>
| EqProp:        \<open>\<stileturn> Member pos x e # EqAtom pos x y # Member pos y e # \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e # EqAtom pos x y # \<Gamma>\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<stileturn> Member pos x e1 # Member pos y e2 # \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e1 # EqAtom neg x y # Member pos y e2 # \<Gamma>\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<stileturn> Member pos x e # Member pos y e # \<Gamma>\<Longrightarrow> \<stileturn> Member pos x e # (EqAtom pos x y) # \<Gamma>\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<stileturn> (Member pos x e) # (Member pos y ec) # \<Gamma> \<Longrightarrow>  
                 \<stileturn> (Member pos x e) # (EqAtom neg x y) # \<Gamma>\<close>
| Close:         \<open>empty_intersection_set rs \<Longrightarrow> \<stileturn> map (\<lambda>r. Member pos x r) rs\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member pos x r) fs) @ \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e # (map (\<lambda>r. Member pos x r) fs) @ \<Gamma>\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<stileturn> Member pos x e # \<Gamma>  \<Longrightarrow>  \<stileturn> (map (\<lambda>r. Member pos x r) (fs)) @ \<Gamma>\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop e e1 e2 \<Longrightarrow> \<stileturn> [(Member pos x e), (EqAtom pos x (Fun ''concat'' [x1,x2])), (Member pos (Var x1) e1), (Member pos (Var x2) e2)] @ \<Gamma>
                 \<Longrightarrow> \<stileturn> [(EqAtom pos x (Fun ''concat'' [x1,x2])), (Member pos (Var x1) e1), (Member pos (Var x2) e2)] @ \<Gamma>\<close>  
| Fwd_ElimConc:  \<open>con_fwd_prop_elim e e1 e2 \<Longrightarrow> \<stileturn> [Member pos x e, (Member pos (Var x1) e1), (Member pos (Var x2) e2)]  @ \<Gamma> \<Longrightarrow>  
                 \<stileturn> [(EqAtom pos x (Fun ''concat'' [x1, x2])), (Member pos (Var x1) e1), (Member pos (Var x2) e2)] @ \<Gamma>\<close>
(*| Bwd_PropConc:  \<open>con_bwd_prop e = es \<Longrightarrow> \<stileturn> ((\<lambda>r. [Member x e, EqAtom x (Fun ''concat'' [x1,x2]), Member (Var x1) (fst r), Member (Var x2) (snd r)] @ \<Gamma>) ` es) \<Longrightarrow> 
                 \<stileturn> {[Member x e, EqAtom x (Fun ''concat'' [x1,x2])] @ \<Gamma>}\<close>*)
| Order:         \<open>\<stileturn> G \<Longrightarrow> set G = set G' \<Longrightarrow> \<stileturn> G'\<close>
| Basic:        \<open> \<stileturn> [A,Neg A, G]\<close>
| BasicFF: \<open>\<stileturn> FF # G\<close>

declare One_SC.intros [intro]

subsection \<open>Soundness\<close>

lemma SC_soundness: \<open>\<stileturn> G \<Longrightarrow> (\<exists>p \<in> set G. \<not> \<lbrakk>E, concat_str\<rbrakk> p)\<close>
proof (induct G rule: One_SC.induct)
  case (Intersect e fs x \<Gamma>)
  then show ?case  apply auto 
    by (smt (verit) INT_I image_subset_iff semantics_fm.simps(4) sup.cobounded1)
qed (auto simp:l_prod_elim is_singleton_def)

(*next
  case (Bwd_PropConc e es x1 x2 x \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def) sorry*)

definition SC_proof :: \<open>string form list \<Rightarrow> string form \<Rightarrow> bool\<close> where
  \<open>SC_proof ps p \<equiv> (\<stileturn>  Neg p # ps)\<close>

theorem sc_soundness:
  \<open>SC_proof ps p \<Longrightarrow> list_all \<lbrakk>E, concat_str\<rbrakk> ps \<Longrightarrow> \<lbrakk>E, concat_str\<rbrakk> p\<close>
  using SC_soundness unfolding SC_proof_def list_all_def
  by fastforce

subsection \<open>Consistent sets\<close>

definition consistency :: "string form set set \<Rightarrow> bool" where
  "consistency C = (\<forall>S. S \<in> C \<longrightarrow> FF \<notin> S \<and> 
              (\<forall> A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
              (\<forall> A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and> 
              (\<forall> A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and> 
              (\<forall> A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and> 
              (\<forall> A. Neg (Neg A) \<in> S \<longrightarrow> S \<union> {A} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> Member neg x e \<in> S \<longrightarrow> S \<union> {Member pos x ec} \<in> C ) \<and> 
              (\<forall> x y f xs. EqAtom neg  x (Fun f xs) \<in> S \<longrightarrow> S \<union> {EqAtom neg  x y, EqAtom pos y (Fun f xs)} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> S \<union> {Member pos x e} \<in> C \<or> S \<union> {Member pos x ec} \<in> C) \<and> 
              (\<forall> x y e. Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x y, Member pos y e} \<in> C) \<and> 
              (\<forall> e1 e2 x y. regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> S \<and> EqAtom neg  x y \<in> S \<and> Member pos y e2 \<in> S \<longrightarrow> S \<union> {Member pos x e1, Member pos y e2} \<in> C) \<and>
              (\<forall> x y e. is_singleton (lang e) \<longrightarrow> Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y e} \<in> C) \<and> 
              (\<forall> x y e ec. is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> S \<and> EqAtom neg  x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y ec} \<in> C) \<and> 
              (\<forall> x rs. empty_intersection_set rs \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r) ` (set rs)) \<in> C \<longrightarrow> S \<union> {FF} \<in> C) \<and> 
              (\<forall> x e fs. subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> S \<and> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C) \<and> 
              (\<forall> x e fs. eq_len_intersect e fs \<longrightarrow>  S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> {Member pos x e} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2 f. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (Fun f [x1, x2]) \<in> S \<and> Member pos (Var x1) e1 \<in> S \<and> Member pos (Var x2) e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x (Fun f [x1,x2]), Member pos (Var x1) e1, Member pos (Var x2) e2} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2 f. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (Fun f [x1, x2]) \<in> S \<and> Member pos (Var x1) e1 \<in> S \<and> Member pos (Var x2) e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos (Var x1) e1, Member pos (Var x2) e2} \<in> C) \<and> 
              (\<forall> S'. S' = S \<longrightarrow> S' \<in> C))"

subsection \<open>Completeness\<close>

theorem TCd_consistency:
  assumes inf_param: \<open>infinite (UNIV::'a set)\<close>
  shows \<open>consistency {S:: string form set. \<exists>G. S = set G \<and> \<not> (\<stileturn> G)}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: \<open>string form set\<close>
  assume \<open>S \<in> {set G | G. \<not> (\<stileturn> G)}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G :: \<open>string form list\<close>
    where *: \<open>S = set G\<close> and \<open>\<not> (\<stileturn> G)\<close>
    by blast
  { 
    assume \<open>FF \<in> S\<close>
    then show False
      using * Basic Order \<open>\<not> (\<stileturn> G)\<close> by auto 
  }
  {
    fix A B 
    assume \<open>Con A B \<in> S\<close>
    then show "S \<union> {A, B} \<in> {set G |G. \<not> (\<stileturn> G)}"
      using * \<open>\<not> (\<stileturn> G)\<close> AlphaCon Order apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A B 
    assume \<open>form.Neg (Dis A B) \<in> S\<close>
    then show \<open> S \<union> {form.Neg A, form.Neg B} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaNegOr apply auto
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A B 
    assume \<open>Dis A B \<in> S\<close>
    then show \<open>S \<union> {A} \<in> {set G |G. \<not> (\<stileturn> G)} \<or> S \<union> {B} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaOr apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A B 
    assume \<open>form.Neg (Con A B) \<in> S\<close>
    then show \<open>S \<union> {form.Neg A} \<in> {set G |G. \<not> (\<stileturn> G)} \<or> S \<union> {form.Neg B} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaNegAnd apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A
    assume \<open>form.Neg (form.Neg A) \<in> S\<close>
    then show \<open>S \<union> {A} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaNegNeg apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x e ec 
    assume \<open>regexp_compl e ec\<close> and \<open> Member neg x e \<in> S\<close>
    then show \<open>S \<union> {Member pos x ec} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NotMember apply auto
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x y f xs 
    assume \<open>EqAtom neg x (Fun f xs) \<in> S\<close>
    then show \<open>S \<union> {EqAtom neg x y, EqAtom pos y (Fun f xs)} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NotEq apply auto
      by (metis insert_absorb list.simps(15))
  }






theorem SC_completeness':
  fixes p :: \<open>string form\<close>
  assumes  mod: \<open>\<forall>e f. list_all (eval e f) ps \<Longrightarrow> eval e f p\<close>
  shows \<open>SC_proof ps p\<close>
  apply(rule ccontr)
  sorry


end