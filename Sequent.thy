
section \<open>Sequent Calculus\<close>

theory Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Multiset" Comparison_Sort_Lower_Bound.Linorder_Relations 
begin

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and formulae are defined as follows:
\<close>
datatype ('f) tm  = Var nat |  Fun 'f \<open>'f tm list\<close> 

datatype sign = pos | neg

datatype ('f) form = 
    EqAtom sign "'f tm" "'f tm"
  | EqFresh sign "'f tm" "'f tm"
  | ConcEq "'f tm" "'f tm" "'f tm"
  | Member sign "'f tm" "char BA rexp"
  | MemberFresh sign "'f tm" "char BA rexp"
  | Dis "'f form" "'f form"                     
  | Con "'f form" "'f form"                      
  | Neg "'f form"     
  | FF
  | TT

subsection \<open>Fresh term\<close>

fun fresh_var :: "nat => 'f tm => bool" where
  "fresh_var x (Var y) = (x \<noteq> y)" |
  "fresh_var x (Fun f xs) = (list_all (\<lambda>a. fresh_var x a) xs)" 

primrec deX :: "'f tm => nat list" where 
  "deX (Var n) = [n] "|
  "deX (Fun f xs) = concat (map deX xs)"

definition
  freshVar :: "string tm list => string tm" where
  "freshVar vs = Var (LEAST n. n \<notin> set (concat (map deX vs)))"

lemma "freshVar [Var (0::nat), Var 1, Var 3] = Var 2"
  apply (auto simp: freshVar_def Least_def)
  using Zero_not_Suc bot_nat_0.extremum by fastforce

subsection \<open>Semantics of term and form\<close>

primrec semantics_tm and semantics_list where
  \<open>semantics_tm e f (Var n) = e n\<close> |
  \<open>semantics_tm e f (Fun i l) = f i (semantics_list e f l)\<close> |
  \<open>semantics_list e f [] = []\<close> |
  \<open>semantics_list e f (t # l) = semantics_tm e f t # semantics_list e f l\<close>

fun concat_str :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "concat_str s ls = (if s = ''concat'' then List.concat ls else [])"

primrec semantics_fm (\<open>\<lbrakk>_, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>E, F\<rbrakk> (EqAtom s x y) = (if s = pos then semantics_tm E F x = semantics_tm E F y else semantics_tm E F x \<noteq> semantics_tm E F y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (EqFresh s x y) = True\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (ConcEq z x y) = (semantics_tm E F z = semantics_tm E F x @ semantics_tm E F y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Member s x r) = (if s = pos then semantics_tm E F x \<in> lang r else semantics_tm E F x \<notin> lang r)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (MemberFresh s x r) = True\<close> 
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
  "member_var_rexp (x#xs) (y#ys) = (if (length xs = length ys) then (Member pos (Var x) y) # (member_var_rexp xs ys) else [])"

fun con_fwd_prop ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop r e1 r2 = (lang (r) = lang (Times e1 r2))"

fun con_fwd_prop_elim ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop_elim r e1 e2 = (lang r = lang (Times e1 e2) \<and> is_singleton (lang r))"

primrec con_bwd_prop ::" char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
  "con_bwd_prop Zero = {(Zero, Zero)}"|
  "con_bwd_prop 1\<^sub>r = {(One, One)}"|
  "con_bwd_prop (Pred a) = {(Pred a, One), (One ,Pred a)}"|
  "con_bwd_prop (Plus r1 r2) = {(Plus r1 r2, One), (One, Plus r1 r2)}"|
  "con_bwd_prop (Times r1 r2) = {(r1, r2), (One ,Times r1 r2), (Times r1 r2, One)}"|
  "con_bwd_prop (Inter r1 r2) = {(One ,Inter r1 r2), (Inter r1 r2, One)}"| (*FIXME: Not Enumerate*)
  "con_bwd_prop (Star r) = {(Star r, Star r)}"

inductive One_SC :: \<open>string form list * string form list set \<Rightarrow> bool\<close> (\<open>\<stileturn> _\<close> 0) where
  AlphaCon:      \<open>\<stileturn> ([Con A B] @ \<Gamma>, {[A,B] @ \<Gamma>})\<close>
| AlphaNegOr:    \<open>\<stileturn> (Neg (Dis A B)# \<Gamma>, {Neg A #Neg B#\<Gamma>})\<close>
| AlphaOr:       \<open>\<stileturn> ([Dis A B, \<Gamma>], {[A, \<Gamma>], [B, \<Gamma>]})\<close>
| AlphaNegAnd:   \<open>\<stileturn> (Neg (Con A B) # \<Gamma>, {Neg A # \<Gamma>, Neg B # \<Gamma>})\<close>
| AlphaNegNeg:   \<open>\<stileturn> (Neg (Neg A) # \<Gamma>, {A# \<Gamma>})\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> ((Member neg x e) # \<Gamma>, {(Member pos x ec) # \<Gamma>})\<close>
| NotEq:         \<open>y = freshVar ([x,(Fun f xs)])  \<Longrightarrow> \<stileturn> ([EqAtom neg x (Fun f xs), \<Gamma>], {[EqFresh neg x y,  EqFresh pos y (Fun f xs), \<Gamma>]})\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> (\<Gamma>, {Member pos x e # \<Gamma>, Member pos x ec # \<Gamma>})\<close>
| EqProp:        \<open>\<stileturn> (Member pos x e # EqAtom pos x y # \<Gamma>, { Member pos x e # EqAtom pos x y # Member pos y e # \<Gamma>})\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<stileturn> (Member pos x e1 # EqAtom neg x y # Member pos y e2 # \<Gamma>, {Member pos x e1 # Member pos y e2 # \<Gamma>})\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<stileturn> (Member pos x e # (EqAtom pos x y) # \<Gamma>, {Member pos x e # Member pos y e # \<Gamma>})\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<stileturn> ((Member pos x e) # (EqAtom neg x y) # \<Gamma>, {(Member pos x e) # (Member pos y ec) # \<Gamma>})\<close>
| Close:         \<open>empty_intersection_set rs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member pos x r) rs, {})\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<stileturn> (Member pos x e # (map (\<lambda>r. Member pos x r) fs) @ \<Gamma>, {(map (\<lambda>r. Member pos x r) fs) @ \<Gamma>})\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<stileturn> ((map (\<lambda>r. Member pos x r) (fs)) @ \<Gamma>, {Member pos x e # \<Gamma>})\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop e e1 e2 \<Longrightarrow> \<stileturn> ([(EqAtom pos x (Fun ''concat'' [x1,x2])), (Member pos x1 e1), (Member pos x2 e2)] @ \<Gamma>, 
{[(Member pos x e), (EqAtom pos x (Fun ''concat'' [x1,x2])), (Member pos x1 e1), (Member pos x2 e2)] @ \<Gamma>})\<close>  

| Fwd_ElimConc:  \<open>con_fwd_prop_elim e e1 e2 \<Longrightarrow> \<stileturn> ([(EqAtom pos x (Fun ''concat'' [x1, x2])), (Member pos x1 e1), (Member pos x2 e2)] @ \<Gamma>,
{ [Member pos x e, (Member pos x1 e1), (Member pos x2 e2)]  @ \<Gamma>})\<close>

| Bwd_PropConc:  \<open>con_bwd_prop e \<noteq> {} \<Longrightarrow> \<stileturn> ([(EqAtom pos x (Fun ''concat'' [x1, x2])), (Member pos x e), \<Gamma>] ,
(\<lambda>r. [Member pos x e, EqAtom pos x (Fun ''concat'' [x1, x2]), (MemberFresh pos x1 (fst r)), (MemberFresh pos x2 (snd r)), \<Gamma>]) ` con_bwd_prop e)\<close>
| Order:         \<open>set G = set G' \<Longrightarrow> \<stileturn> (G', {G})\<close>
| Basic:        \<open> \<stileturn> ([A,Neg A, G], {})\<close>
 
declare One_SC.intros [intro]

subsection \<open>Soundness\<close>

lemma SC_soundness: \<open>\<stileturn> G \<Longrightarrow> (\<forall>fs \<in> (snd G). \<exists>f \<in> set fs. \<not> \<lbrakk>E, concat_str\<rbrakk> f) \<Longrightarrow> (\<exists>p \<in> set (fst G). \<not> \<lbrakk>E, concat_str\<rbrakk> p) \<close>
proof (induct rule: One_SC.induct)
  case (NeqPropElim e ec x y \<Gamma>)
  then show ?case apply auto 
    by (metis (no_types, lifting) DiffI UNIV_I is_singletonE singletonD) 
next
  case (Intersect e fs x \<Gamma>)
  then show ?case apply auto 
    by (smt (verit, del_insts) INT_I image_subset_iff semantics_fm.simps(4) sup.cobounded1) 
qed (auto simp:l_prod_elim is_singleton_def)

subsection \<open>Consistent sets\<close>

definition consistency :: \<open>string form set set \<Rightarrow> bool\<close> where
  \<open>consistency C = (\<forall>S. S \<in> C \<longrightarrow> FF \<notin> S \<and> 
               (\<forall>p q. \<not> (EqAtom pos p q \<in> S \<and> EqAtom neg  p q \<in> S) \<and>
               \<not> (\<forall>x r. Member pos x r \<in> S \<and> Member pos x r \<in> S)) \<and> 
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
              (\<forall> x x1 x2 e e1 e2 f. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (Fun f [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x (Fun f [x1,x2]), Member pos x1 e1, Member pos x2 e2} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2 f. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (Fun f [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos x1 e1, Member pos x2 e2} \<in> C) \<and> 
              (\<forall> S'. S' = S \<longrightarrow> S' \<in> C))\<close>

subsection \<open>Completeness\<close>

theorem SC_completeness':
  fixes p :: \<open>string form\<close>
  assumes  mod: \<open>\<forall>e f. list_all (eval e f) ps \<longrightarrow> eval e f p\<close>
  shows \<open>SC_proof ps p\<close>
  apply(rule ccontr)
  sorry


end