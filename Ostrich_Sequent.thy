theory Ostrich_Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Countable"
begin

section \<open>Miscellaneous Utilities\<close>

text \<open>Some facts about (in)finite sets\<close>

theorem set_inter_compl_diff [simp]: \<open>- A \<inter> B = B - A\<close> by blast

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:tms} The datatypes of tms and formulae are defined as follows:
\<close>
datatype ('a) tm  = Var nat  |  App 'a \<open>'a tm list\<close> 

datatype sign = pos | neg

datatype ('a, 'b) form = 
    FF
  | TT
  | EqAtom sign "'a tm" "'a tm"
  | EqFresh sign "'a tm" "'a tm"
  | ConcEq "'a tm" "'a tm" "'a tm"
  | Member sign "'a tm" "'b rexp"
  | Dis "('a, 'b) form" "('a, 'b) form"
  | Con "('a, 'b) form" "('a, 'b) form"
  | Neg "('a, 'b) form"

primrec size_form :: \<open>('a, 'b) form \<Rightarrow> nat\<close> where
  \<open>size_form FF = 0\<close>
| \<open>size_form TT = 0\<close>
| \<open>size_form (EqAtom s p q) = 0\<close>
| \<open>size_form (EqFresh s p q) = 0\<close>
| \<open>size_form (ConcEq f p q) = 0\<close>
| \<open>size_form (Member s p r) = 0\<close>
| \<open>size_form (Dis p q) = size_form p + size_form q + 1\<close>
| \<open>size_form (Con p q) = size_form p + size_form q + 1\<close>
| \<open>size_form (Neg p) = size_form p + 1\<close>

subsection \<open>Fresh tm\<close>

fun fresh_var :: "nat => 'a tm => bool" where
  "fresh_var x (Var y) = (x \<noteq> y)" |
  "fresh_var x (App f xs) = (list_all (\<lambda>a. fresh_var x a) xs)" 

primrec deX :: "'a tm => nat list" where 
  "deX (Var n) = [n] "|
  "deX (App f xs) = (concat (map deX xs))"

definition
  freshVar :: "string tm list => string tm" where
  "freshVar vs = Var (LEAST n. n \<notin> set (concat (map deX vs)))"

lemma "freshVar [Var (0::nat), Var 1, Var 3] = Var 2"
  apply (auto simp: freshVar_def Least_def)
  using Zero_not_Suc bot_nat_0.extremum by fastforce

subsection \<open>Parameters\<close>

primrec
  paramst :: \<open>'a tm \<Rightarrow> 'a set\<close> and
  paramsts :: \<open>'a tm list \<Rightarrow> 'a set\<close> where
  \<open>paramst (Var n) = {}\<close>
| \<open>paramst (App a ts) = {a} \<union> paramsts ts\<close>
| \<open>paramsts [] = {}\<close>
| \<open>paramsts (t # ts) = (paramst t \<union> paramsts ts)\<close>

primrec params :: \<open>('a,'b) form \<Rightarrow> 'a set\<close> where
  \<open>params FF = {}\<close>
| \<open>params TT = {}\<close>
| \<open>params (EqAtom s p q) = paramst p \<union> paramst q\<close>
| \<open>params (EqFresh s p q) = paramst p \<union> paramst q\<close>
| \<open>params (Dis p q) = params p \<union> params q\<close>
| \<open>params (Con p q) = params p \<union> params q\<close>
| \<open>params (Neg p) = params p\<close>
| \<open>params (ConcEq m p q) = {}\<close>
| \<open>params (Member s x r) = {}\<close>

subsection \<open>Closed terms and formulae\<close>

text \<open>
Many of the results proved in the following sections are restricted
to closed terms and formulae. We call a term or formula {\em closed at
level \<open>i\<close>}, if it only contains ``loose'' bound variables with
indices smaller than \<open>i\<close>.
\<close>

primrec
  closedt :: \<open>nat \<Rightarrow> 'a tm \<Rightarrow> bool\<close> and
  closedts :: \<open>nat \<Rightarrow> 'a tm list \<Rightarrow> bool\<close> where
  \<open>closedt m (Var n) = (n < m)\<close>
| \<open>closedt m (App a ts) = closedts m ts\<close>
| \<open>closedts m [] = True\<close>
| \<open>closedts m (t # ts) = (closedt m t \<and> closedts m ts)\<close>

primrec closed :: \<open>nat \<Rightarrow> ('a, 'b) form \<Rightarrow> bool\<close> where
  \<open>closed m FF = True\<close>
| \<open>closed m TT = True\<close>
| \<open>closed m (EqAtom s p q) = (closedt m p \<and> closedt m q)\<close>
| \<open>closed m (EqFresh s p q) = (closedt m p \<and> closedt m q)\<close>
| \<open>closed m (ConcEq c p q) = (closedt m p \<and> closedt m q \<and> closedt m c)\<close>
| \<open>closed m (Member s x r) = (closedt m x)\<close>
| \<open>closed m (Con p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Dis p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Neg p) = closed m p\<close>

theorem closedt_mono: assumes le: \<open>i \<le> j\<close>
  shows \<open>closedt i (t::'a tm) \<Longrightarrow> closedt j t\<close>
    and \<open>closedts i (ts::'a tm list) \<Longrightarrow> closedts j ts\<close>
  using le by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem closed_mono: assumes le: \<open>i \<le> j\<close>
  shows \<open>closed i p \<Longrightarrow> closed j p\<close>
  using le
proof (induct p arbitrary: i j)
qed (auto simp: closedt_mono(1))

section \<open>Semantics\<close>


primrec
  evalt :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a tm \<Rightarrow> 'c\<close> and
  evalts :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a tm list \<Rightarrow> 'c list\<close> where
  \<open>evalt e f (Var n) = e n\<close>
| \<open>evalt e f (App a ts) = f a (evalts e f ts)\<close>
| \<open>evalts e f [] = []\<close>
| \<open>evalts e f (t # ts) = evalt e f t # evalts e f ts\<close>


fun concat_str :: "nat \<Rightarrow> string list \<Rightarrow> string" where
  "concat_str s ls = (if s = 1 then List.concat ls else [])"

primrec eval :: "(nat \<Rightarrow> 'a list) \<Rightarrow> ('b \<Rightarrow> 'a list list \<Rightarrow> 'a list) \<Rightarrow> ('b, 'a BA) form \<Rightarrow> bool" (\<open>\<lbrakk>_, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>E, F\<rbrakk> (EqAtom s x y) = (if s = pos then evalt E F x = evalt E F y else evalt E F x \<noteq> evalt E F y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (EqFresh s x y) = True\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (ConcEq z x y) = (evalt E F z = evalt E F x @ evalt E F y)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Member s x r) = (if s = pos then evalt E F x \<in> lang r else evalt E F x \<notin> lang r)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (Dis x y) = (\<lbrakk>E, F\<rbrakk> x \<or> \<lbrakk>E, F\<rbrakk> y)\<close>
| \<open>\<lbrakk>E, F\<rbrakk> (Con x y) = (\<lbrakk>E, F\<rbrakk> x \<and> \<lbrakk>E, F\<rbrakk> y)\<close>
| \<open>\<lbrakk>E, F\<rbrakk> (Neg x) = (\<not> \<lbrakk>E, F\<rbrakk> x)\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (FF) = False\<close> 
| \<open>\<lbrakk>E, F\<rbrakk> (TT) = True\<close> 

section \<open>Proof calculus\<close>

fun is_Member :: "('a, 'b) form \<Rightarrow> bool" where 
  "is_Member (Member s x r)  = True"|
  "is_Member _ = False"

fun variable_in_member :: "('a, 'b) form \<Rightarrow> 'a tm option" where 
  "variable_in_member (Member s x r) = Some x"|
  "variable_in_member _ = None"

fun rexp_in_member :: "('a, 'b) form \<Rightarrow> 'b rexp" where 
  "rexp_in_member (Member s x r) = r"

definition "distinct_variable  ls = distinct (map (variable_in_member) ls)"

definition "single_word ls = (List.find (\<lambda>r. \<not> is_singleton (lang r)) (map (rexp_in_member) ls) = None)"

fun exists_solution :: "(nat, char BA) form list \<Rightarrow> bool" where
  "exists_solution ls = (if ls = [] then False 
                       else list_all is_Member ls \<and> distinct_variable ls \<and> single_word ls)"  

fun empty_intersection_set :: "char BA rexp list \<Rightarrow> bool" where
  "empty_intersection_set fs = (\<Inter>(lang ` set fs) = {})"

fun subset_intersect_set :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "subset_intersect_set r fs = (\<Inter>(lang ` set fs) \<subseteq> lang r)"

fun eq_len_intersect :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "eq_len_intersect r fs = (\<Inter>(lang ` set fs) = lang r \<and> length fs > 1)"

fun member_var_rexp :: "nat list \<Rightarrow> char BA rexp list \<Rightarrow> (nat, char BA) form list" where 
  "member_var_rexp [] b = []"|
  "member_var_rexp (v # va) [] = []"|
  "member_var_rexp (x#xs) (y#ys) = (if (length xs = length ys) then (Member pos (Var x) y) # (member_var_rexp xs ys) else [])"

fun con_fwd_prop ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop r r1 r2 = (lang r = lang (Times r1 r2))"

fun con_fwd_prop_elim ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop_elim r e1 e2 = (lang r = lang (Times e1 e2) \<and> is_singleton (lang r))"

fun con_bwd_prop ::" char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
  "con_bwd_prop r = {(a,b)|a b. lang r = (lang (Times a b))}"


inductive One_SC :: \<open>(nat, char BA) form list \<Rightarrow> bool\<close> (\<open>\<stileturn> _\<close> 0) where
  AlphaCon:      \<open>\<stileturn> [A,B] @ \<Gamma> \<Longrightarrow> \<stileturn> [Con A B] @ \<Gamma>\<close>
| AlphaNegOr:    \<open>\<stileturn> [Neg A, Neg B] @\<Gamma> \<Longrightarrow> \<stileturn> Neg (Dis A B)# \<Gamma>\<close>
| AlphaOr:       \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> B# \<Gamma> \<Longrightarrow> \<stileturn> Dis A B # \<Gamma>\<close>
| AlphaNegAnd:   \<open>\<stileturn> Neg A # \<Gamma> \<Longrightarrow>  \<stileturn> Neg B # \<Gamma> \<Longrightarrow> \<stileturn> Neg (Con A B) # \<Gamma>\<close>
| AlphaNegNeg:   \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> Neg (Neg A) # \<Gamma>\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> (Member pos x ec) # \<Gamma> \<Longrightarrow> \<stileturn> (Member neg x e) # \<Gamma>\<close>
| NotEq:         \<open>\<stileturn> [EqFresh neg x y,  EqFresh pos y (App f xs)] @ \<Gamma> \<Longrightarrow> \<stileturn> [EqAtom neg x (App f xs)]  @ \<Gamma>\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> Member pos x e # \<Gamma> \<Longrightarrow>  \<stileturn> Member pos x ec # \<Gamma> \<Longrightarrow>  \<stileturn> \<Gamma>\<close>
| EqProp:        \<open>\<stileturn> Member pos x e # EqAtom pos x y # Member pos y e # \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e # EqAtom pos x y # \<Gamma>\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<stileturn> Member pos x e1 # Member pos y e2 # \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e1 # EqAtom neg x y # Member pos y e2 # \<Gamma>\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<stileturn> Member pos x e # Member pos y e # \<Gamma>\<Longrightarrow> \<stileturn> Member pos x e # (EqAtom pos x y) # \<Gamma>\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<stileturn> (Member pos x e) # (Member pos y ec) # \<Gamma> \<Longrightarrow>  
                 \<stileturn> (Member pos x e) # (EqAtom neg x y) # \<Gamma>\<close>
| Close:         \<open>length rs > 1 \<Longrightarrow> empty_intersection_set rs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member pos x r) rs) @ \<Gamma>\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member pos x r) fs) @ \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e # (map (\<lambda>r. Member pos x r) fs) @ \<Gamma>\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<stileturn> Member pos x e # \<Gamma>  \<Longrightarrow>  \<stileturn> (map (\<lambda>r. Member pos x r) (fs)) @ \<Gamma>\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop e e1 e2 \<Longrightarrow> \<stileturn> [(Member pos x e), (EqAtom pos x (App 1 [x1,x2])), (Member pos (x1) e1), (Member pos (x2) e2)] @ \<Gamma>
                 \<Longrightarrow> \<stileturn> [(EqAtom pos x (App 1 [x1,x2])), (Member pos (x1) e1), (Member pos (x2) e2)] @ \<Gamma>\<close>  
| Fwd_ElimConc:  \<open>con_fwd_prop_elim e e1 e2 \<Longrightarrow> \<stileturn> [Member pos x e, (Member pos (x1) e1), (Member pos (x2) e2)]  @ \<Gamma> \<Longrightarrow>  
                 \<stileturn> [(EqAtom pos x (App 1 [x1, x2])), (Member pos (x1) e1), (Member pos (x2) e2)] @ \<Gamma>\<close>
(*| Bwd_PropConc:  \<open>con_bwd_prop e = es \<Longrightarrow> \<stileturn> ((\<lambda>r. [Member x e, EqAtom x (App 1 [x1,x2]), Member (x1) (fst r), Member (x2) (snd r)] @ \<Gamma>) ` es) \<Longrightarrow> 
                 \<stileturn> {[Member x e, EqAtom x (App 1 [x1,x2])] @ \<Gamma>}\<close>*)
| Order:         \<open>\<stileturn> G \<Longrightarrow> set G = set G' \<Longrightarrow> \<stileturn> G'\<close>
| Basic:         \<open>\<stileturn> [A,Neg A, G]\<close>


declare One_SC.intros [intro]

section \<open>Soundness\<close>

lemma aux_close : "Suc 0 < |rs| \<Longrightarrow>  \<Inter> (Symbolic_Regular_Algebra_Model.lang ` set rs) = {} \<Longrightarrow> \<exists>p\<in>Member pos x ` set rs . \<not> \<lbrakk>E, \<lambda>a b. if a = 1 then concat b else []\<rbrakk> p"
  apply auto
  done

lemma One_SC_soundness: \<open>\<stileturn> G \<Longrightarrow> (\<exists>p \<in> set G. \<not> \<lbrakk>E, concat_str\<rbrakk> p)\<close>
proof (induct G rule: One_SC.induct)
  case (Close rs x \<Gamma>)
  then show ?case apply auto
  proof -
    assume a1:"Suc 0 < |rs|" and a2:"\<Inter> (Symbolic_Regular_Algebra_Model.lang ` set rs) = {}"
    then have "\<exists>p\<in>Member pos x ` set rs. \<not> \<lbrakk>E, \<lambda>a b. if a = Suc 0 then concat b else []\<rbrakk> p" by auto
    then show "\<exists>p\<in>Member pos x ` set rs \<union> set \<Gamma>. \<not> \<lbrakk>E, \<lambda>a b. if a = Suc 0 then concat b else []\<rbrakk> p" 
      by blast
  qed
next
  case (Intersect e fs x \<Gamma>)
  then show ?case  apply auto 
    by (smt (verit) INT_I image_subset_iff eval.simps(4) sup.cobounded1)
qed (auto simp:l_prod_elim is_singleton_def)

(*next
  case (Bwd_PropConc e es x1 x2 x \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def) sorry*)

definition One_SC_proof :: \<open>(nat, char BA) form list \<Rightarrow> (nat, char BA) form \<Rightarrow> bool\<close> where
  \<open>One_SC_proof ps p \<equiv> (\<stileturn>  Neg p # ps)\<close>

theorem sc_soundness:
  \<open>One_SC_proof ps p \<Longrightarrow> list_all \<lbrakk>E, concat_str\<rbrakk> ps \<Longrightarrow> \<lbrakk>E, concat_str\<rbrakk> p\<close>
  using One_SC_soundness unfolding One_SC_proof_def list_all_def
  by fastforce

section \<open>Completeness\<close>  


subsection \<open>Consistent sets\<close>

definition consistency :: "(nat, char BA) form set set \<Rightarrow> bool" where
  "consistency C = (\<forall>S. S \<in> C \<longrightarrow> 
              (\<forall> A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
              (\<forall> A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and> 
              (\<forall> A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and> 
              (\<forall> A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and> 
              (\<forall> A. Neg (Neg A) \<in> S \<longrightarrow> S \<union> {A} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> Member neg x e \<in> S \<longrightarrow> S \<union> {Member pos x ec} \<in> C) \<and> 
              (\<forall> x y f xs. EqAtom neg  x (App f xs) \<in> S \<longrightarrow> S \<union> {EqFresh neg  x y, EqFresh pos y (App f xs)} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> S \<union> {Member pos x e} \<in> C \<longrightarrow> S \<union> {Member pos x ec} \<in> C \<longrightarrow> S \<in> C) \<and> 
              (\<forall> x y e. Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x y, Member pos y e} \<in> C) \<and> 
              (\<forall> e1 e2 x y. regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> S \<and> EqAtom neg  x y \<in> S \<and> Member pos y e2 \<in> S \<longrightarrow> S \<union> {Member pos x e1, Member pos y e2} \<in> C) \<and>
              (\<forall> x y e. is_singleton (lang e) \<longrightarrow> Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y e} \<in> C) \<and> 
              (\<forall> x y e ec. is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> S \<and> EqAtom neg  x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y ec} \<in> C) \<and> 
              (\<forall> x rs. length rs > 1 \<longrightarrow> empty_intersection_set rs \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r) ` (set rs)) \<notin> C) \<and> 
              (\<forall> x e fs. subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> S \<and> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C) \<and> 
              (\<forall> x e fs. eq_len_intersect e fs \<longrightarrow>  S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> {Member pos x e} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (App 1 [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x (App 1 [x1,x2]), Member pos x1 e1, Member pos x2 e2} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (App 1 [x1, x2]) \<in> S \<and> Member pos (x1) e1 \<in> S \<and> Member pos (x2) e2 \<in> S \<longrightarrow> S \<union> {EqAtom pos x (App 1 [x1,x2]), Member pos x e, Member pos (x1) e1, Member pos (x2) e2} \<in> C) \<and> 
              (\<forall> S'. S' = S \<longrightarrow> S' \<in> C))"

theorem One_SC_consistency:
  assumes inf_param: \<open>infinite (UNIV::'a set)\<close>
  shows \<open>consistency {S:: (nat, char BA) form set. \<exists>G. S = set G \<and> \<not> (\<stileturn> G)}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: \<open>(nat, char BA) form set\<close>
  assume \<open>S \<in> {set G | G. \<not> (\<stileturn> G)}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G :: \<open>(nat, char BA) form list\<close>
    where *: \<open>S = set G\<close> and \<open>\<not> (\<stileturn> G)\<close>
    by blast
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
    assume \<open>EqAtom neg x (App f xs) \<in> S\<close>
    then show \<open>S \<union> {EqFresh neg x y, EqFresh pos y (App f xs)} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NotEq apply auto
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x e ec
    assume \<open>regexp_compl e ec\<close> and \<open>S \<union> {Member pos x e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close> and\<open>S \<union> {Member pos x ec} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show \<open>S \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Cut 
      by blast 
  }
  {
    fix x y e
    assume \<open>Member pos x e \<in> S \<and> EqAtom pos x y \<in> S\<close>
    then show \<open>S \<union> {Member pos x e, EqAtom pos x y, Member pos y e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order EqProp apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix e1 e2 x y
    assume \<open>regexp_empty e1 e2\<close> and \<open>Member pos x e1 \<in> S \<and> EqAtom neg x y \<in> S \<and> Member pos y e2 \<in> S\<close>
    then show \<open>S \<union> {Member pos x e1, Member pos y e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NeqSubsume apply auto done
  }
  {
    fix x y e
    assume \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> and \<open>Member pos x e \<in> S \<and> EqAtom pos x y \<in> S\<close>
    then show \<open>S \<union> {Member pos x e, Member pos y e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order EqPropElim apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x y e ec
    assume \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> and
       \<open>regexp_compl e ec\<close> and
       \<open>Member pos x e \<in> S \<and> EqAtom neg x y \<in> S\<close>
    then show \<open>S \<union> {Member pos x e, Member pos y ec} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NeqPropElim apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x rs
    assume \<open> 1 < |rs|\<close> and \<open>empty_intersection_set rs\<close> and  \<open>S \<union> Member pos x ` set rs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show False
      using * \<open>\<not> (\<stileturn> G)\<close> Order Close apply auto 
      by (metis (no_types, lifting) list.set_map set_append sup_commute)
  }
  {
    fix x e fs
    assume \<open>subset_intersect_set e fs\<close> and \<open>Member pos x e \<in> S \<and> S \<union> Member pos x ` set fs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show \<open>S \<union> Member pos x ` set fs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Subsume apply auto done
  }
  {
    fix x e fs
    assume \<open>eq_len_intersect e fs\<close> and \<open>S \<union> Member pos x ` set fs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show \<open>S \<union> {Member pos x e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Intersect apply auto 
      by (metis (no_types, lifting) list.set_map list.simps(15) set_append sup_commute)
  }
  {
    fix x x1 x2 e e1 e2
    assume \<open>con_fwd_prop e e1 e2\<close> and \<open>EqAtom pos x (App 1 [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Member pos x e # EqAtom pos x (App 1 [x1, x2]) # Member pos x1 e1# Member pos x2 e2 # G)\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_PropConc apply auto  
      by (smt (verit, del_insts) insert_absorb list.simps(15))
    moreover have \<open>S \<union> {Member pos x e,EqAtom pos x (App 1 [x1, x2]),Member pos x1 e1, Member pos x2 e2} = set (Member pos x e # EqAtom pos x (App 1 [x1, x2]) # Member pos x1 e1# Member pos x2 e2 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Member pos x e, EqAtom pos x (App 1 [x1, x2]), Member pos x1 e1, Member pos x2 e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_PropConc by auto 
  }
  {
    fix S'
    assume \<open>S \<in> {set G |G. \<not> (\<stileturn> G)}\<close> and \<open>S' = S\<close>
    then show \<open>S' \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using \<open>\<not> (\<stileturn> G)\<close> by auto
  }
  {
    fix x x1 x2 e e1 e2 
    assume \<open>con_fwd_prop_elim e e1 e2\<close> and \<open>EqAtom pos x (App 1 [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then have \<open>\<not> (\<stileturn> EqAtom pos x (App 1 [x1, x2])# Member pos x e# Member pos x1 e1#  Member pos x2 e2 # G)\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_ElimConc apply auto 
      by (smt (verit, del_insts) insert_absorb list.set_intros(2) list.simps(15))
    moreover have \<open>S \<union> {EqAtom pos x (App 1 [x1, x2]), Member pos x e, Member pos x1 e1,  Member pos x2 e2} = set (EqAtom pos x (App 1 [x1, x2])# Member pos x e# Member pos x1 e1#  Member pos x2 e2 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {EqAtom pos x (App 1 [x1, x2]), Member pos x e, Member pos x1 e1, Member pos x2 e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using \<open>\<not> (\<stileturn> G)\<close> by auto 
  }
qed


subsection \<open>Closure\<close>


definition close :: \<open>('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set\<close> where
  \<open>close C = {S. \<exists>S' \<in> C. S \<subseteq> S'}\<close>

definition subset_closed :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>subset_closed C = (\<forall>S' \<in> C. \<forall>S. S \<subseteq> S' \<longrightarrow> S \<in> C)\<close>


lemma subset_in_close:
  assumes \<open>S \<subseteq> S'\<close>
  shows \<open>S' \<union> x \<in> C \<longrightarrow> S \<union> x \<in> close C\<close>
proof -
  have \<open>S' \<union> x \<in> close C \<longrightarrow> S \<union> x \<in> close C\<close>
    unfolding close_def using \<open>S \<subseteq> S'\<close> by blast
  then show ?thesis unfolding close_def by blast
qed

theorem close_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>consistency (close C)\<close>
  unfolding consistency_def
proof (intro allI impI conjI)
  fix S
  assume \<open>S \<in> close C\<close>
  then obtain x where \<open>x \<in> C\<close> and \<open>S \<subseteq> x\<close>
    unfolding close_def by blast

  {
    fix A B
    assume \<open>Con A B \<in> S\<close>
    then have \<open>Con A B \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {A, B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by force
    then show \<open>S \<union> {A, B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  } 
  {
    fix A B
    assume \<open>Neg (Dis A B) \<in> S\<close>
    then have \<open>Neg (Dis A B) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Neg A, Neg B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by force
    then show \<open>S \<union> {Neg A, Neg B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix A B
    assume \<open>Dis A B \<in> S\<close>
    then have \<open>Dis A B \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {A} \<in> C \<or> x \<union> {B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {A} \<in> close C \<or> S \<union> {B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix A B
    assume \<open>Neg (Con A B) \<in> S\<close>
    then have \<open>Neg (Con A B) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Neg A} \<in> C \<or> x \<union> {Neg B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {Neg A} \<in> close C \<or> S \<union> {Neg B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix A
    assume \<open>Neg (Neg A) \<in> S\<close>
    then have \<open>Neg (Neg A) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {A} \<in> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {A} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix y e ec
    assume \<open>regexp_compl e ec\<close> and \<open>Member neg y e \<in> S\<close>
    then have \<open>Member neg y e \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Member pos y ec} \<in> C\<close>
      using \<open>regexp_compl e ec\<close> \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {Member pos y ec} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix a b f xs
    assume \<open>EqAtom neg a (App f xs) \<in> S\<close>
    then have \<open>EqAtom neg a (App f xs) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {EqFresh neg a b, EqFresh pos b (App f xs)} \<in> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {EqFresh neg a b, EqFresh pos b (App f xs)} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    (*FIXME bug?*)
    fix a e ec
    assume \<open>regexp_compl e ec\<close> and  \<open>S \<union> {Member pos a e} \<in> close C\<close> 
        and \<open>S \<union> {Member pos a ec} \<in> close C\<close>
    then show \<open>S \<in> close C\<close> 
      using \<open>S \<in> close C\<close> by simp
  }
  {
    fix a b e
    assume \<open>Member pos a e \<in> S \<and> EqAtom pos a b \<in> S\<close>
    then have \<open>Member pos a e \<in> x \<and> EqAtom pos a b \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>(x \<union> {Member pos a e, EqAtom pos a b, Member pos b e} \<in> C)\<close>
      using \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {Member pos a e, EqAtom pos a b, Member pos b e} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  } 
  {
    fix e1 e2 a b
    assume \<open>regexp_empty e1 e2\<close> and \<open>Member pos a e1 \<in> S \<and> EqAtom neg a b \<in> S \<and> Member pos b e2 \<in> S\<close>
    then have \<open>Member pos a e1 \<in> x \<and> EqAtom neg a b \<in> S \<and> Member pos b e2 \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Member pos a e1, Member pos b e2} \<in> C\<close>
      by (metis \<open>x \<in> C\<close> bot.extremum insert_subset sup.absorb_iff1)
    then show \<open>S \<union> {Member pos a e1, Member pos b e2} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix a b e
    assume \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> and \<open>Member pos a e \<in> S \<and> EqAtom pos a b \<in> S\<close>
    then have \<open>Member pos a e \<in> x \<and> EqAtom pos a b \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Member pos a e, Member pos b e} \<in> C\<close>
      using \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {Member pos a e, Member pos b e} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix a b e ec
    assume \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> and 
      \<open>regexp_compl e ec\<close> and 
      \<open>Member pos a e \<in> S \<and> EqAtom neg a b \<in> S\<close>
    then have \<open>Member pos a e \<in> x \<and> EqAtom neg a b \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Member pos a e, Member pos b ec} \<in> C\<close>
      using \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> \<open>regexp_compl e ec\<close> \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> {Member pos a e, Member pos b ec} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast
  }
  {
    fix a rs 
    assume \<open>1 < |rs|\<close> and \<open>empty_intersection_set rs\<close> 
    then have \<open>x \<union> Member pos a ` set rs \<notin> C\<close>
      using \<open>x \<in> C\<close> conc consistency_def by auto
    then show \<open>S \<union> Member pos a ` set rs \<notin> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close sorry
  }
  {
    fix a e fs
    assume \<open>subset_intersect_set e fs\<close> and \<open>Member pos a e \<in> S \<and> S \<union> Member pos a ` set fs \<in> close C\<close>
    then show \<open>S \<union> Member pos a ` set fs \<in> close C\<close>
      by blast 
  }
  {
    fix a e fs
    assume \<open>eq_len_intersect e fs\<close> and \<open>S \<union> Member pos a ` set fs \<in> close C\<close>
    then show \<open>S \<union> {Member pos a e} \<in> close C\<close>
      sorry
  }
  {
    fix a x1 x2 e e1 e2
    assume \<open>con_fwd_prop e e1 e2\<close> and \<open>EqAtom pos a (App 1 [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then show \<open>S \<union> {Member pos a e, EqAtom pos a (App 1 [x1, x2]), Member pos x1 e1, Member pos x2 e2} \<in> close C\<close>
      sorry
  }
  {
    fix a x1 x2 e e1 e2
    assume \<open>con_fwd_prop_elim e e1 e2\<close> and \<open>EqAtom pos a (App 1 [x1, x2]) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then show \<open>S \<union> {EqAtom pos a (App 1 [x1, x2]), Member pos a e, Member pos x1 e1, Member pos x2 e2} \<in> close C\<close>
      sorry
  }
  {
    fix S'
    assume \<open>S' = S\<close>
    then show \<open>S' \<in> close C\<close>
      by (simp add: \<open>S \<in> close C\<close>)
  }
qed

theorem close_closed: \<open>subset_closed (close C)\<close>
  unfolding close_def subset_closed_def by blast

theorem close_subset: \<open>C \<subseteq> close C\<close>
  unfolding close_def by blast

subsection \<open>Finite character\<close>


definition finite_char :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>finite_char C = (\<forall>S. S \<in> C = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C))\<close>

definition mk_finite_char :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>mk_finite_char C = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> C}\<close>


theorem finite_alt_consistency:
  assumes altconc: \<open>consistency C\<close>
    and \<open>subset_closed C\<close>
  shows \<open>consistency (mk_finite_char C)\<close>
  unfolding consistency_def
sorry


theorem finite_char: \<open>finite_char (mk_finite_char C)\<close>
  unfolding finite_char_def mk_finite_char_def by blast

theorem finite_char_closed: \<open>finite_char C \<Longrightarrow> subset_closed C\<close>
  unfolding finite_char_def subset_closed_def
proof (intro ballI allI impI)
  fix S S'
  assume *: \<open>\<forall>S. (S \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C)\<close>
    and \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C\<close> by blast
  then show \<open>S \<in> C\<close> using * by blast
qed

theorem finite_char_subset: \<open>subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast


subsection \<open>Enumerating datatypes\<close>

instance \<open>rexp\<close> :: (countable) countable
  by countable_datatype

instance \<open>tm\<close> :: (countable) countable
  by countable_datatype

instance \<open>sign\<close> :: countable
  by countable_datatype

instance form :: (countable,countable) countable 
  by countable_datatype
  
subsection \<open>Extension to maximal consistent set\<close>


text \<open>
\label{sec:extend}
Given a set \<open>C\<close> of finite character, we show that
the least upper bound of a chain of sets that are elements
of \<open>C\<close> is again an element of \<open>C\<close>.
\<close>

definition is_chain :: \<open>(nat \<Rightarrow> 'a set) \<Rightarrow> bool\<close> where
  \<open>is_chain f = (\<forall>n. f n \<subseteq> f (Suc n))\<close>

theorem is_chainD: \<open>is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f (m + n)\<close>
  by (induct n) (auto simp: is_chain_def)

theorem is_chainD':
  assumes \<open>is_chain f\<close> and \<open>x \<in> f m\<close> and \<open>m \<le> k\<close>
  shows \<open>x \<in> f k\<close>
proof -
  have \<open>\<exists>n. k = m + n\<close>
    using \<open>m \<le> k\<close> by (simp add: le_iff_add)
  then obtain n where \<open>k = m + n\<close>
    by blast
  then show \<open>x \<in> f k\<close>
    using \<open>is_chain f\<close> \<open>x \<in> f m\<close>
    by (simp add: is_chainD)
qed

theorem chain_index:
  assumes ch: \<open>is_chain f\<close> and fin: \<open>finite F\<close>
  shows \<open>F \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>n. F \<subseteq> f n\<close>
  using fin
proof (induct rule: finite_induct)
  case empty
  then show ?case by blast
next
  case (insert x F)
  then have \<open>\<exists>n. F \<subseteq> f n\<close> and \<open>\<exists>m. x \<in> f m\<close> and \<open>F \<subseteq> (\<Union>x. f x)\<close>
    using ch by simp_all
  then obtain n and m where \<open>F \<subseteq> f n\<close> and \<open>x \<in> f m\<close>
    by blast
  have \<open>m \<le> max n m\<close> and \<open>n \<le> max n m\<close>
    by simp_all
  have \<open>x \<in> f (max n m)\<close>
    using is_chainD' ch \<open>x \<in> f m\<close> \<open>m \<le> max n m\<close> by fast
  moreover have \<open>F \<subseteq> f (max n m)\<close>
    using is_chainD' ch \<open>F \<subseteq> f n\<close> \<open>n \<le> max n m\<close> by fast
  moreover have \<open>x \<in> f (max n m) \<and> F \<subseteq> f (max n m)\<close>
    using calculation by blast
  ultimately show ?case by blast
qed

lemma chain_union_closed':
  assumes \<open>is_chain f\<close> and \<open>(\<forall>n. f n \<in> C)\<close> and \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    and \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>S' \<in> C\<close>
proof -
  note \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  then obtain n where \<open>S' \<subseteq> f n\<close>
    using chain_index \<open>is_chain f\<close> by blast
  moreover have \<open>f n \<in> C\<close>
    using \<open>\<forall>n. f n \<in> C\<close> by blast
  ultimately show \<open>S' \<in> C\<close>
    using \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close> by blast
qed

theorem chain_union_closed:
  assumes \<open>finite_char C\<close> and \<open>is_chain f\<close> and \<open>\<forall>n. f n \<in> C\<close>
  shows \<open>(\<Union>n. f n) \<in> C\<close>
proof -
  have \<open>subset_closed C\<close>
    using finite_char_closed \<open>finite_char C\<close> by blast
  then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using subset_closed_def by blast
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C\<close>
    using chain_union_closed' assms by blast
  moreover have \<open>((\<Union>n. f n) \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C)\<close>
    using \<open>finite_char C\<close> unfolding finite_char_def by blast
  ultimately show ?thesis by blast
qed

primrec extend :: \<open>(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> nat \<Rightarrow> (nat, 'b) form set\<close> where
  \<open>extend S C f 0 = S\<close>
| \<open>extend S C f (Suc n) = (if extend S C f n \<union> {f n} \<in> C
     then extend S C f n \<union> {f n}
     else extend S C f n)\<close>

definition Extend :: \<open>(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> (nat, 'b) form set\<close> where
  \<open>Extend S C f = (\<Union>n. extend S C f n)\<close>

theorem is_chain_extend: \<open>is_chain (extend S C f)\<close>
  by (simp add: is_chain_def) blast

theorem finite_paramst [simp]: \<open>finite (paramst (t :: 'a tm))\<close>
  \<open>finite (paramsts (ts :: 'a tm list))\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all split: sum.split)

theorem finite_params [simp]: \<open>finite (params p)\<close>
  by (induct p) simp_all

theorem finite_params_extend [simp]:
  \<open>infinite (\<Inter>p \<in> S. - params p) \<Longrightarrow> infinite (\<Inter>p \<in> extend S C f n. - params p)\<close>
  by(induct n)  auto 

lemma infinite_params_available:
  assumes \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  shows \<open>\<exists>x. x \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)\<close>
proof -
  let ?S' = \<open>extend S C f n \<union> {f n}\<close>

  have \<open>infinite (- (\<Union>x \<in> ?S'. params x))\<close>
    using assms by simp
  then obtain x where \<open>x \<in> - (\<Union>x \<in> ?S'. params x)\<close>
    using infinite_imp_nonempty by blast
  then have \<open>\<forall>a \<in> ?S'. x \<notin> params a\<close>
    by blast
  then show ?thesis
    by blast
qed


lemma extend_in_C_stop:
  assumes \<open>extend S C f n \<in> C\<close>
    and \<open>extend S C f n \<union> {f n} \<notin> C\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
  using assms by simp

theorem extend_in_C: \<open>consistency C \<Longrightarrow>
  S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> extend S C f n \<in> C\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by auto
qed

text \<open>
The main theorem about \<open>Extend\<close> says that if \<open>C\<close> is an
alternative consistency property that is of finite character,
\<open>S\<close> is consistent and \<open>S\<close> uses only finitely many
parameters, then \<open>Extend S C f\<close> is again consistent.
\<close>

theorem Extend_in_C: \<open>consistency C \<Longrightarrow> finite_char C \<Longrightarrow>
  S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> Extend S C f \<in> C\<close>
  unfolding Extend_def
  using chain_union_closed is_chain_extend extend_in_C
  by blast

theorem Extend_subset: \<open>S \<subseteq> Extend S C f\<close>
proof
  fix x
  assume \<open>x \<in> S\<close>
  then have \<open>x \<in> extend S C f 0\<close> by simp
  then have \<open>\<exists>n. x \<in> extend S C f n\<close> by blast
  then show \<open>x \<in> Extend S C f\<close> by (simp add: Extend_def)
qed

text \<open>
The \<open>Extend\<close> function yields a maximal set:
\<close>

definition maximal :: \<open>'a set \<Rightarrow> 'a set set \<Rightarrow> bool\<close> where
  \<open>maximal S C = (\<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S')\<close>

theorem extend_maximal:
  assumes \<open>\<forall>y. \<exists>n. y = f n\<close>
    and \<open>finite_char C\<close>
  shows \<open>maximal (Extend S C f) C\<close>
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume \<open>S' \<in> C\<close>
    and \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close>
  moreover have \<open>S' \<subseteq> (\<Union>x. extend S C f x)\<close>
  proof (rule ccontr)
    assume \<open>\<not> S' \<subseteq> (\<Union>x. extend S C f x)\<close>
    then have \<open>\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
    then obtain z where \<open>z \<in> S'\<close> and *: \<open>z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
    then obtain n where \<open>z = f n\<close>
      using \<open>\<forall>y. \<exists>n. y = f n\<close> by blast

    from \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close> \<open>z = f n\<close> \<open>z \<in> S'\<close>
    have \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close> by blast

    from \<open>finite_char C\<close>
    have \<open>subset_closed C\<close> using finite_char_closed by blast
    then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      unfolding subset_closed_def by simp
    then have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
      using \<open>S' \<in> C\<close> by blast
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close>
      by blast
    then have \<open>z \<in> extend S C f (Suc n)\<close>
      using \<open>z \<notin> (\<Union>x. extend S C f x)\<close> \<open>z = f n\<close>
      by simp
    then show False using * by blast
  qed
  ultimately show \<open>(\<Union>x. extend S C f x) = S'\<close>
    by simp
qed


subsection \<open>Hintikka sets and Herbrand models\<close>

text \<open>
\label{sec:hintikka}
A Hintikka set is defined as follows:
\<close>

definition hintikka :: \<open>('a, char BA) form set \<Rightarrow> bool\<close> where
  \<open>hintikka H =
     ((\<forall>A. \<not> (A \<in> H \<and> Neg A \<in> H)) \<and>
     FF \<notin> H \<and> Neg TT \<notin> H \<and>
     (\<forall>Z. Neg (Neg Z) \<in> H \<longrightarrow> Z \<in> H) \<and>
     (\<forall>A B. Con A B \<in> H \<longrightarrow> A \<in> H \<and> B \<in> H) \<and>
     (\<forall>A B. Neg (Dis A B) \<in> H \<longrightarrow> Neg A \<in> H \<and> Neg B \<in> H) \<and>
     (\<forall>A B. Dis A B \<in> H \<longrightarrow> A \<in> H \<or> B \<in> H) \<and>
     (\<forall>A B. Neg (Con A B) \<in> H \<longrightarrow> Neg A \<in> H \<or> Neg B \<in> H) \<and>
     (\<forall>x e ec. regexp_compl e ec \<longrightarrow> Member neg x e \<in> H \<longrightarrow> Member pos x ec \<in> H) \<and> 
     (\<forall>x y f xs. EqAtom neg x (App f xs) \<in> H \<longrightarrow> EqFresh neg x y \<in> H \<and> EqFresh pos y (App f xs) \<in> H) \<and>
     (\<forall>x e ec. regexp_compl e ec \<longrightarrow> Member pos x e \<in> H \<or> Member pos x ec \<in> H) \<and> 
     (\<forall>x y e. Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<and> Member pos y e \<in> H) \<and> 
     (\<forall> e1 e2 x y. regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> H \<and> EqAtom neg  x y \<in> H \<and> Member pos y e2 \<in> H \<longrightarrow> Member pos x e1 \<in> H \<and> Member pos y e2 \<in> H) \<and>
     (\<forall> x y e. is_singleton (lang e) \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> Member pos y e \<in> H) \<and> 
     (\<forall> x y e ec. is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> H \<and> EqAtom neg  x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> Member pos y ec \<in> H) \<and> 
     (\<forall> x rs. length rs > 1 \<longrightarrow> empty_intersection_set rs \<longrightarrow> ((\<lambda>r. Member pos x r) ` (set rs)) \<subseteq> H) \<and> 
     (\<forall> x e fs. subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> H \<and> ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H \<longrightarrow> ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H) \<and> 
     (\<forall> x e fs. eq_len_intersect e fs \<longrightarrow>  ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H \<longrightarrow> Member pos x e \<in> H) \<and> 
     (\<forall> x x1 x2 f e e1 e2. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (App f [x1, x2]) \<in> H \<and> Member pos x1 e1 \<in> H \<and> Member pos x2 e2 \<in> H \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x (App f [x1,x2]) \<in> H \<and> Member pos x1 e1 \<in> H \<and> Member pos x2 e2 \<in> H) \<and> 
     (\<forall> x x1 x2 f e e1 e2. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (App f [x1, x2]) \<in> H \<and> Member pos (x1) e1 \<in> H \<and> Member pos (x2) e2 \<in> H \<longrightarrow> EqAtom pos x (App f [x1,x2]) \<in> H \<and> Member pos x e \<in> H \<and> Member pos (x1) e1 \<in> H \<and> Member pos (x2) e2 \<in> H))\<close>

text \<open>
In Herbrand models, each {\em closed} term is interpreted by itself.
We introduce a new datatype \<open>hterm\<close> (``Herbrand terms''), which
is similar to the datatype \<open>term\<close> introduced in \secref{sec:terms},
but without variables. We also define functions for converting between
closed terms and Herbrand terms.
\<close>

datatype 'a hterm = HApp 'a \<open>'a hterm list\<close>

primrec
  term_of_hterm :: \<open>'a hterm \<Rightarrow> 'a tm\<close> and
  terms_of_hterms :: \<open>'a hterm list \<Rightarrow> 'a tm list\<close> where
  \<open>term_of_hterm (HApp a hts) = App a (terms_of_hterms hts)\<close>
| \<open>terms_of_hterms [] = []\<close>
| \<open>terms_of_hterms (ht # hts) = term_of_hterm ht # terms_of_hterms hts\<close>

theorem herbrand_evalt [simp]:
  \<open>closedt 0 t \<Longrightarrow> term_of_hterm (evalt e HApp t) = t\<close>
  \<open>closedts 0 ts \<Longrightarrow> terms_of_hterms (evalts e HApp ts) = ts\<close>
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem herbrand_evalt' [simp]:
  \<open>evalt e HApp (term_of_hterm ht) = ht\<close>
  \<open>evalts e HApp (terms_of_hterms hts) = hts\<close>
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

theorem closed_hterm [simp]:
  \<open>closedt 0 (term_of_hterm (ht::'a hterm))\<close>
  \<open>closedts 0 (terms_of_hterms (hts::'a hterm list))\<close>
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

text \<open>
We can prove that Hintikka sets are satisfiable in Herbrand models.
Note that this theorem cannot be proved by a simple structural induction
(as claimed in Fitting's book), since a parameter substitution has
to be applied in the cases for quantifiers. However, since parameter
substitution does not change the size of formulae, the theorem can
be proved by well-founded induction on the size of the formula \<open>p\<close>.
\<close>

theorem hintikka_model:
  assumes hin: \<open>hintikka H\<close>
  shows \<open>(p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) p) \<and>
  (Neg p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>                                    
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg p))\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size_form\<close>])
  show \<open>wf (measure size_form)\<close>
    by blast
next
  let ?eval = \<open>eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H)\<close>

  fix x
  assume wf: \<open>\<forall>y. (y, x) \<in> measure size_form \<longrightarrow>
                  (y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?eval y) \<and>
              (Neg y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?eval (Neg y))\<close>

  show \<open>(x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?eval x) \<and> (Neg x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?eval (Neg x))\<close>
  proof (cases x)
    case FF
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close>
      then show \<open>?eval x\<close>
        using FF hin by (simp add: hintikka_def)
    next
      assume \<open>Neg x \<in> H\<close>
      then show \<open>?eval (Neg x)\<close> using FF by simp
    qed
  next
    case TT
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close>
      then show \<open>?eval x\<close>
        using TT by simp
    next
      assume \<open>Neg x \<in> H\<close>
      then show \<open>?eval (Neg x)\<close>
        using TT hin by (simp add: hintikka_def)
    qed
  next
    case (Pred p ts)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then show \<open>?eval x\<close> using Pred by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Pred p ts) \<in> H\<close>
        using Pred by simp
      then have \<open>Pred p ts \<notin> H\<close>
        using hin unfolding hintikka_def by fast
      then show \<open>?eval (Neg x)\<close>
        using Pred \<open>closed 0 x\<close> by simp
    qed
  next
    case (Neg Z)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then show \<open>?eval x\<close>
        using Neg wf by simp
    next
      assume \<open>Neg x \<in> H\<close>
      then have \<open>Z \<in> H\<close>
        using Neg hin unfolding hintikka_def by blast
      moreover assume \<open>closed 0 x\<close>
      then have \<open>closed 0 Z\<close>
        using Neg by simp
      ultimately have \<open>?eval Z\<close>
        using Neg wf by simp
      then show \<open>?eval (Neg x)\<close>
        using Neg by simp
    qed
  next
    case (And A B)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>And A B \<in> H\<close> and \<open>closed 0 (And A B)\<close>
        using And by simp_all
      then have \<open>A \<in> H \<and> B \<in> H\<close>
        using And hin unfolding hintikka_def by blast
      then show \<open>?eval x\<close>
        using And wf \<open>closed 0 (And A B)\<close> by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (And A B) \<in> H\<close> and \<open>closed 0 (And A B)\<close>
        using And by simp_all
      then have \<open>Neg A \<in> H \<or> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval (Neg x)\<close>
        using And wf \<open>closed 0 (And A B)\<close> by fastforce
    qed
  next
    case (Or A B)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Or A B \<in> H\<close> and \<open>closed 0 (Or A B)\<close>
        using Or by simp_all
      then have \<open>A \<in> H \<or> B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval x\<close>
        using Or wf \<open>closed 0 (Or A B)\<close> by fastforce
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Or A B) \<in> H\<close> and \<open>closed 0 (Or A B)\<close>
        using Or by simp_all
      then have \<open>Neg A \<in> H \<and> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval (Neg x)\<close>
        using Or wf \<open>closed 0 (Or A B)\<close> by simp
    qed
  next
    case (Impl A B)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Impl A B \<in> H\<close> and \<open>closed 0 (Impl A B)\<close>
        using Impl by simp_all
      then have \<open>Neg A \<in> H \<or> B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval x\<close>
        using Impl wf \<open>closed 0 (Impl A B)\<close> by fastforce
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Impl A B) \<in> H\<close> and \<open>closed 0 (Impl A B)\<close>
        using Impl by simp_all
      then have \<open>A \<in> H \<and> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval (Neg x)\<close>
        using Impl wf \<open>closed 0 (Impl A B)\<close> by simp
    qed
  next
    case (Forall P)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      have \<open>\<forall>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
      proof (rule allI)
        fix z
        from \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
        have \<open>Forall P \<in> H\<close> and \<open>closed 0 (Forall P)\<close>
          using Forall by simp_all
        then have *: \<open>\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> H \<longrightarrow> P[t/0] \<in> H\<close>
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Forall P)\<close>
        have \<open>closed (Suc 0) P\<close> by simp

        have \<open>(P[term_of_hterm z/0], Forall P) \<in> measure size_form \<longrightarrow>
              (P[term_of_hterm z/0] \<in> H \<longrightarrow> closed 0 (P[term_of_hterm z/0]) \<longrightarrow>
              ?eval (P[term_of_hterm z/0]))\<close>
          using Forall wf by blast
        then show \<open>eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
          using * \<open>Forall P \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show \<open>?eval x\<close>
        using Forall by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Forall P) \<in> H\<close>
        using Forall by simp
      then have \<open>\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> H\<close>
        using Forall hin unfolding hintikka_def by blast
      then obtain t where *: \<open>closedt 0 t \<and> Neg (P[t/0]) \<in> H\<close>
        by blast
      then have \<open>closed 0 (P[t/0])\<close>
        using Forall \<open>closed 0 x\<close> by simp

      have \<open>(subst P t 0, Forall P) \<in> measure size_form \<longrightarrow>
              (Neg (subst P t 0) \<in> H \<longrightarrow> closed 0 (subst P t 0) \<longrightarrow>
              ?eval (Neg (subst P t 0)))\<close>
        using Forall wf by blast
      then have \<open>?eval (Neg (P[t/0]))\<close>
        using Forall * \<open>closed 0 (P[t/0])\<close> by simp
      then have \<open>\<exists>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
        by auto
      then show \<open>?eval (Neg x)\<close>
        using Forall by simp
    qed
  next
    case (Exists P)
    then show ?thesis
    proof (intro conjI impI allI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>\<exists>t. closedt 0 t \<and> (P[t/0]) \<in> H\<close>
        using Exists hin unfolding hintikka_def by blast
      then obtain t where *: \<open>closedt 0 t \<and> (P[t/0]) \<in> H\<close>
        by blast
      then have \<open>closed 0 (P[t/0])\<close>
        using Exists \<open>closed 0 x\<close> by simp

      have \<open>(subst P t 0, Exists P) \<in> measure size_form \<longrightarrow>
              ((subst P t 0) \<in> H \<longrightarrow> closed 0 (subst P t 0) \<longrightarrow>
              ?eval (subst P t 0))\<close>
        using Exists wf by blast
      then have \<open>?eval (P[t/0])\<close>
        using Exists * \<open>closed 0 (P[t/0])\<close> by simp
      then have \<open>\<exists>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
        by auto
      then show \<open>?eval x\<close>
        using Exists by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      have \<open>\<forall>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
      proof (rule allI)
        fix z
        from \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
        have \<open>Neg (Exists P) \<in> H\<close> and \<open>closed 0 (Neg (Exists P))\<close>
          using Exists by simp_all
        then have *: \<open>\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> H \<longrightarrow> Neg (P[t/0]) \<in> H\<close>
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Neg (Exists P))\<close>
        have \<open>closed (Suc 0) P\<close> by simp

        have \<open>(P[term_of_hterm z/0], Exists P) \<in> measure size_form \<longrightarrow>
              (Neg (P[term_of_hterm z/0]) \<in> H \<longrightarrow> closed 0 (P[term_of_hterm z/0]) \<longrightarrow>
              ?eval (Neg (P[term_of_hterm z/0])))\<close>
          using Exists wf by blast
        then show \<open>\<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
          using * \<open>Neg (Exists P) \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show \<open>?eval (Neg x)\<close>
        using Exists by simp
    qed
  qed
qed

text \<open>
Using the maximality of @{term \<open>Extend S C f\<close>}, we can show
that @{term \<open>Extend S C f\<close>} yields Hintikka sets:
\<close>

lemma Exists_in_extend:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>Exists P = f n\<close>
  shows \<open>P[(App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])/0] \<in>
          extend S C f (Suc n)\<close>
    (is \<open>subst P ?t 0 \<in> extend S C f (Suc n)\<close>)
proof -
  have \<open>\<exists>p. f n = Exists p\<close>
    using \<open>Exists P = f n\<close> by metis
  then have \<open>extend S C f (Suc n) = (?S' \<union> {(dest_Exists (f n))[?t/0]})\<close>
    using \<open>?S' \<in> C\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {(dest_Exists (Exists P))[?t/0]})\<close>
    using \<open>Exists P = f n\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {P[?t/0]})\<close>
    by simp
  finally show ?thesis
    by blast
qed

lemma Neg_Forall_in_extend:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>Neg (Forall P) = f n\<close>
  shows \<open>Neg (P[(App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])/0])  \<in>
          extend S C f (Suc n)\<close>
    (is \<open>Neg (subst P ?t 0) \<in> extend S C f (Suc n)\<close>)
proof -
  have \<open>f n \<noteq> Exists P\<close>
    using \<open>Neg (Forall P) = f n\<close> by auto

  have \<open>\<exists>p. f n = Neg (Forall p)\<close>
    using \<open>Neg (Forall P) = f n\<close> by metis
  then have \<open>extend S C f (Suc n) = (?S' \<union> {Neg (dest_Forall (dest_Neg (f n))[?t/0])})\<close>
    using \<open>?S' \<in> C\<close> \<open>f n \<noteq> Exists P\<close> by auto
  also have \<open>\<dots> = (?S' \<union> {Neg (dest_Forall (dest_Neg (Neg (Forall P)))[?t/0])})\<close>
    using \<open>Neg (Forall P) = f n\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {Neg (P[?t/0])})\<close>
    by simp
  finally show ?thesis
    by blast
qed

theorem extend_hintikka:
  assumes fin_ch: \<open>finite_char C\<close>
    and infin_p: \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and surj: \<open>\<forall>y. \<exists>n. y = f n\<close>
    and altc: \<open>alt_consistency C\<close>
    and \<open>S \<in> C\<close>
  shows \<open>hintikka (Extend S C f)\<close> (is \<open>hintikka ?H\<close>)
  unfolding hintikka_def
proof (intro allI impI conjI)
  have \<open>maximal ?H C\<close>
    by (simp add: extend_maximal fin_ch surj)

  have \<open>?H \<in> C\<close>
    using Extend_in_C assms by blast

  have \<open>\<forall>S' \<in> C. ?H \<subseteq> S' \<longrightarrow> ?H = S'\<close>
    using \<open>maximal ?H C\<close>
    unfolding maximal_def by blast

  { fix p ts
    show \<open>\<not> (Pred p ts \<in> ?H \<and> Neg (Pred p ts) \<in> ?H)\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast }

  show \<open>FF \<notin> ?H\<close>
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast

  show \<open>Neg TT \<notin> ?H\<close>
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast

  { fix Z
    assume \<open>Neg (Neg Z) \<in> ?H\<close>
    then have \<open>?H \<union> {Z} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>Z \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>And A B \<in> ?H\<close>
    then have \<open>?H \<union> {A, B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>A \<in> ?H\<close> and \<open>B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Neg (Or A B) \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A, Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>Neg A \<in> ?H\<close> and \<open>Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Neg (Impl A B) \<in> ?H\<close>
    then have \<open>?H \<union> {A, Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>A \<in> ?H\<close> and \<open>Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Or A B \<in> ?H\<close>
    then have \<open>?H \<union> {A} \<in> C \<or> ?H \<union> {B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>A \<in> ?H \<or> B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Neg (And A B) \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A} \<in> C \<or> ?H \<union> {Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by simp
    then show \<open>Neg A \<in> ?H \<or> Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Impl A B \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A} \<in> C \<or> ?H \<union> {B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by simp
    then show \<open>Neg A \<in> ?H \<or> B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P and t :: \<open>nat term\<close>
    assume \<open>Forall P \<in> ?H\<close> and \<open>closedt 0 t\<close>
    then have \<open>?H \<union> {P[t/0]} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>P[t/0] \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P and t :: \<open>nat term\<close>
    assume \<open>Neg (Exists P) \<in> ?H\<close> and \<open>closedt 0 t\<close>
    then have \<open>?H \<union> {Neg (P[t/0])} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>Neg (P[t/0]) \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P
    assume \<open>Exists P \<in> ?H\<close>
    obtain n where *: \<open>Exists P = f n\<close>
      using surj by blast

    let ?t = \<open>App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []\<close>
    have \<open>closedt 0 ?t\<close> by simp

    have \<open>Exists P \<in> (\<Union>n. extend S C f n)\<close>
      using \<open>Exists P \<in> ?H\<close> Extend_def by blast
    then have \<open>extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)\<close>
      using * by (simp add: UN_upper)
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    then have \<open>P[?t/0] \<in> extend S C f (Suc n)\<close>
      using * Exists_in_extend by blast
    then have \<open>P[?t/0] \<in> ?H\<close>
      using Extend_def by blast
    then show \<open>\<exists>t. closedt 0 t \<and> P[t/0] \<in> ?H\<close>
      using \<open>closedt 0 ?t\<close> by blast }

  { fix P
    assume \<open>Neg (Forall P) \<in> ?H\<close>
    obtain n where *: \<open>Neg (Forall P) = f n\<close>
      using surj by blast

    let ?t = \<open>App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []\<close>
    have \<open>closedt 0 ?t\<close> by simp

    have \<open>Neg (Forall P) \<in> (\<Union>n. extend S C f n)\<close>
      using \<open>Neg (Forall P) \<in> ?H\<close> Extend_def by blast
    then have \<open>extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)\<close>
      using * by (simp add: UN_upper)
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    then have \<open>Neg (P[?t/0]) \<in> extend S C f (Suc n)\<close>
      using * Neg_Forall_in_extend by blast
    then have \<open>Neg (P[?t/0]) \<in> ?H\<close>
      using Extend_def by blast
    then show \<open>\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> ?H\<close>
      using \<open>closedt 0 ?t\<close> by blast }
qed

subsection \<open>Model existence theorem\<close>

text \<open>
\label{sec:model-existence}
Since the result of extending \<open>S\<close> is a superset of \<open>S\<close>,
it follows that each consistent set \<open>S\<close> has a Herbrand model:
\<close>

lemma hintikka_Extend_S:
  assumes \<open>consistency C\<close> and \<open>S \<in> C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  shows \<open>hintikka (Extend S (mk_finite_char (mk_alt_consistency (close C))) from_nat)\<close>
    (is \<open>hintikka (Extend S ?C' from_nat)\<close>)
proof -
  have \<open>finite_char ?C'\<close>
    using finite_char by blast
  moreover have \<open>\<forall>y. y = from_nat (to_nat y)\<close>
    by simp
  then have \<open>\<forall>y. \<exists>n. y = from_nat n\<close>
    by blast
  moreover have \<open>alt_consistency ?C'\<close>
    using alt_consistency close_closed close_consistency \<open>consistency C\<close>
      finite_alt_consistency mk_alt_consistency_closed
    by blast
  moreover have \<open>S \<in> close C\<close>
    using close_subset \<open>S \<in> C\<close> by blast
  then have \<open>S \<in> mk_alt_consistency (close C)\<close>
    using mk_alt_consistency_subset by blast
  then have \<open>S \<in> ?C'\<close>
    using close_closed finite_char_subset mk_alt_consistency_closed by blast
  ultimately show ?thesis
    using extend_hintikka \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    by metis
qed

theorem model_existence:
  assumes \<open>consistency C\<close>
    and \<open>S \<in> C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>p \<in> S\<close>
    and \<open>closed 0 p\<close>
  shows \<open>eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend S
        (mk_finite_char (mk_alt_consistency (close C))) from_nat) p\<close>
  using assms hintikka_model hintikka_Extend_S Extend_subset
  by blast

subsection \<open>Completeness for Natural Deduction\<close>

theorem One_SC_completeness':
  fixes p :: \<open>(nat, char BA) form\<close>
  assumes  mod: \<open>\<forall>(e :: nat \<Rightarrow> string) f. list_all (eval e f g) ps \<longrightarrow> eval e f g p\<close>
  shows \<open>One_SC_proof ps p\<close>
  sorry


end