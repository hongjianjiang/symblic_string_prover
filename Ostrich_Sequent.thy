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
type_synonym id = String.literal

datatype tm = Var id | Fn id "tm list" | Reg "char BA rexp"

datatype 'a fm = Truth | Falsity | Atom 'a | Imp "'a fm" "'a fm" | Iff "'a fm" "'a fm" |
    And "'a fm" "'a fm" | Or "'a fm" "'a fm" | Not "'a fm"

datatype fol = Rl id "tm list"

term "Atom (Rl (STR '':'') [Var STR ''x'', Reg One])"
term "Atom (Rl (STR ''='') [Var STR ''z'', Fn i [Var STR ''x'', Var STR ''y'']])"

datatype "thm" = Thm (concl: "fol fm")

subsection \<open>Definition of rules and axioms\<close>

abbreviation (input) "fail_thm \<equiv> Thm Truth"

definition fol_equal :: "fol fm \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "fol_equal p q \<equiv> p = q"

definition zip_eq :: "tm list \<Rightarrow> tm list \<Rightarrow> fol fm list"
where
  "zip_eq l l' \<equiv> map (\<lambda>(t, t'). Atom (Rl (STR ''='') [t, t'])) (zip l l')"

primrec occurs_in :: "id \<Rightarrow> tm \<Rightarrow> bool" and occurs_in_list :: "id \<Rightarrow> tm list \<Rightarrow> bool"
where
  "occurs_in i (Var x) = (i = x)" |
  "occurs_in i (Fn _ l) = occurs_in_list i l" |
  "occurs_in_list _ [] = False" |
  "occurs_in_list i (h # t) = (occurs_in i h \<or> occurs_in_list i t)"

primrec free_in :: "id \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "free_in _ Truth = False" |
  "free_in _ Falsity = False" |
  "free_in i (Atom a) = (case a of Rl _ l \<Rightarrow> occurs_in_list i l)" |
  "free_in i (Imp p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Iff p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (And p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Or p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Not p) = free_in i p" 

primrec equal_length :: "tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "equal_length l [] = (case l of [] \<Rightarrow> True | _ # _ \<Rightarrow> False)" |
  "equal_length l (_ # r') = (case l of [] \<Rightarrow> False | _ # l' \<Rightarrow> equal_length l' r')"

subsection \<open>Semantics of first-order logic\<close>

definition length2 :: "tm list \<Rightarrow> bool"
where
  "length2 l \<equiv> case l of [_,_] \<Rightarrow> True | _ \<Rightarrow> False"

primrec \<comment> \<open>Semantics of terms\<close>
  semantics_term :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a" and
  semantics_list :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list"
where
  "semantics_term e _ (Var x) = e x" |
  "semantics_term e f (Fn i l) = f i (semantics_list e f l)" |
  "semantics_list _ _ [] = []" |
  "semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec \<comment> \<open>Semantics of formulas\<close>
  semantics :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "semantics _ _ _ Truth = True" |
  "semantics _ _ _ Falsity = False" |
  "semantics e f g (Atom a) = (case a of Rl i l \<Rightarrow> if i = STR ''='' \<and> length2 l
      then (semantics_term e f (hd l) = semantics_term e f (hd (tl l)))
      else g i (semantics_list e f l))" |
  "semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)" |
  "semantics e f g (Iff p q) = (semantics e f g p \<longleftrightarrow> semantics e f g q)" |
  "semantics e f g (And p q) = (semantics e f g p \<and> semantics e f g q)" |
  "semantics e f g (Or p q) = (semantics e f g p \<or> semantics e f g q)" |
  "semantics e f g (Not p) = (\<not> semantics e f g p)"


subsection \<open>Definition of proof system\<close>

definition addI :: "thm \<Rightarrow> thm \<Rightarrow> thm" where
  "addI s s' \<equiv> let p = concl s in let p' = concl s' in Thm (And p p')"

definition neg_orI :: "thm \<Rightarrow> thm \<Rightarrow> thm" where
  "neg_orI s s' \<equiv> case concl s of Not p \<Rightarrow>
                 (case concl s' of Not q \<Rightarrow> Thm (Not (Or p q)) | _ \<Rightarrow> fail_thm)
                  | _ \<Rightarrow> fail_thm"

definition orI :: "thm \<Rightarrow> thm \<Rightarrow> thm" where
  "orI s s' \<equiv> let p = concl s in let p' = concl s' in Thm (Or p p')"

definition neg_andI :: "thm \<Rightarrow> thm \<Rightarrow> thm" where
  "neg_andI s s' \<equiv>case concl s of Not p \<Rightarrow>
                 (case concl s' of Not q \<Rightarrow> Thm (Not (And p q)) | _ \<Rightarrow> fail_thm)
                  | _ \<Rightarrow> fail_thm"

definition neg_negI :: "thm  \<Rightarrow> thm" where
  "neg_negI s \<equiv> let p = concl s in Thm (Not (Not p))"

definition not_memberI :: "thm  \<Rightarrow> thm" where
  "not_memberI s \<equiv> case concl s of Atom p \<Rightarrow> case p of Rl i l \<Rightarrow> if i = STR '':'' \<and> length2 l
      then  Thm (Atom (Rl STR ''~:'' l))
      else  fail_thm | _ \<Rightarrow> fail_thm"

inductive sequent :: "fol fm list \<Rightarrow> bool" ("\<turnstile> _" 0) where
  andI: "\<turnstile> [concl s, concl s', \<Gamma>] \<Longrightarrow> \<turnstile> [concl (addI s s'), \<Gamma>]" |
  neg_orI: "\<turnstile> [concl s, concl s', \<Gamma>] \<Longrightarrow> \<turnstile> [concl (neg_orI s s'), \<Gamma>]" |
  orI: "\<turnstile> [concl s, \<Gamma>] \<Longrightarrow> \<turnstile> [concl s', \<Gamma>] \<Longrightarrow> \<turnstile> [concl (orI s s'), \<Gamma>]" |
  neg_andI: "\<turnstile> [concl s, \<Gamma>] \<Longrightarrow> \<turnstile> [concl s', \<Gamma>] \<Longrightarrow> \<turnstile> [concl (neg_andI s s'), \<Gamma>]" |
  neg_negI: "\<turnstile> [concl s, \<Gamma>] \<Longrightarrow> \<turnstile> [concl (neg_negI s), \<Gamma>]" |
  not_memberI: "\<turnstile> [concl s, \<Gamma>] \<Longrightarrow> \<turnstile> [concl (not_memberI s), \<Gamma>]"






fun is_Member :: "('a) form \<Rightarrow> bool" where 
  "is_Member (Member s x r)  = True"|
  "is_Member _ = False"

fun variable_in_member :: "('a) form \<Rightarrow> tm option" where 
  "variable_in_member (Member s x r) = Some x"|
  "variable_in_member _ = None"

fun rexp_in_member :: "('b) form \<Rightarrow> 'b rexp" where 
  "rexp_in_member (Member s x r) = r"

definition "distinct_variable  ls = distinct (map (variable_in_member) ls)"

definition "single_word ls = (List.find (\<lambda>r. \<not> is_singleton (lang r)) (map (rexp_in_member) ls) = None)"

fun exists_solution :: "(char BA) form list \<Rightarrow> bool" where
  "exists_solution ls = (if ls = [] then False 
                       else list_all is_Member ls \<and> distinct_variable ls \<and> single_word ls)"  

fun empty_intersection_set :: "char BA rexp list \<Rightarrow> bool" where
  "empty_intersection_set fs = (\<Inter>(lang ` set fs) = {})"

fun subset_intersect_set :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "subset_intersect_set r fs = (\<Inter>(lang ` set fs) \<subseteq> lang r)"

fun eq_len_intersect :: "char BA rexp \<Rightarrow> char BA rexp list \<Rightarrow> bool" where 
  "eq_len_intersect r fs = (\<Inter>(lang ` set fs) = lang r \<and> length fs > 1)"

fun member_var_rexp :: "nat list \<Rightarrow> char BA rexp list \<Rightarrow> (char BA) form list" where 
  "member_var_rexp [] b = []"|
  "member_var_rexp (v # va) [] = []"|
  "member_var_rexp (x#xs) (y#ys) = (if (length xs = length ys) then (Member pos (Var x) y) # (member_var_rexp xs ys) else [])"

fun con_fwd_prop ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop r r1 r2 = (lang r = lang (Times r1 r2))"

fun con_fwd_prop_elim ::"char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" where
  "con_fwd_prop_elim r e1 e2 = (lang r = lang (Times e1 e2) \<and> is_singleton (lang r))"

fun con_bwd_prop ::" char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
  "con_bwd_prop r = {(a,b)|a b. lang r = (lang (Times a b))}"


inductive One_SC :: \<open>(char BA) form list \<Rightarrow> bool\<close> (\<open>\<stileturn> _\<close> 0) where
  AlphaCon:      \<open>\<stileturn> [A,B] @ \<Gamma> \<Longrightarrow> \<stileturn> [Con A B] @ \<Gamma>\<close>
| AlphaNegOr:    \<open>\<stileturn> [Neg A, Neg B] @\<Gamma> \<Longrightarrow> \<stileturn> Neg (Dis A B)# \<Gamma>\<close>
| AlphaOr:       \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> B# \<Gamma> \<Longrightarrow> \<stileturn> Dis A B # \<Gamma>\<close>
| AlphaNegAnd:   \<open>\<stileturn> Neg A # \<Gamma> \<Longrightarrow>  \<stileturn> Neg B # \<Gamma> \<Longrightarrow> \<stileturn> Neg (Con A B) # \<Gamma>\<close>
| AlphaNegNeg:   \<open>\<stileturn> A# \<Gamma> \<Longrightarrow> \<stileturn> Neg (Neg A) # \<Gamma>\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> (Member pos x ec) # \<Gamma> \<Longrightarrow> \<stileturn> (Member neg x e) # \<Gamma>\<close>
| NotEq:         \<open>\<stileturn> [EqFresh neg x y,  EqFresh pos y (Conc x1 x2)] @ \<Gamma> \<Longrightarrow> \<stileturn> [EqAtom neg x (Conc x1 x2)]  @ \<Gamma>\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> Member pos x e # \<Gamma> \<Longrightarrow>  \<stileturn> Member pos x ec # \<Gamma> \<Longrightarrow>  \<stileturn> \<Gamma>\<close>
| EqProp:        \<open>\<stileturn> Member pos x e # EqAtom pos x y # Member pos y e # \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e # EqAtom pos x y # \<Gamma>\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<stileturn> Member pos x e1 # Member pos y e2 # \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e1 # EqAtom neg x y # Member pos y e2 # \<Gamma>\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<stileturn> Member pos x e # Member pos y e # \<Gamma>\<Longrightarrow> \<stileturn> Member pos x e # (EqAtom pos x y) # \<Gamma>\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<stileturn> (Member pos x e) # (Member pos y ec) # \<Gamma> \<Longrightarrow>  
                 \<stileturn> (Member pos x e) # (EqAtom neg x y) # \<Gamma>\<close>
| Close:         \<open>length rs > 1 \<Longrightarrow> empty_intersection_set rs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member pos x r) rs) @ \<Gamma>\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<stileturn> (map (\<lambda>r. Member pos x r) fs) @ \<Gamma> \<Longrightarrow> \<stileturn> Member pos x e # (map (\<lambda>r. Member pos x r) fs) @ \<Gamma>\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<stileturn> Member pos x e # \<Gamma>  \<Longrightarrow>  \<stileturn> (map (\<lambda>r. Member pos x r) (fs)) @ \<Gamma>\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop e e1 e2 \<Longrightarrow> \<stileturn> [(Member pos x e), (EqAtom pos x (Conc x1 x2)), (Member pos (x1) e1), (Member pos (x2) e2)] @ \<Gamma>
                 \<Longrightarrow> \<stileturn> [(EqAtom pos x (Conc x1 x2)), (Member pos x1 e1), (Member pos x2 e2)] @ \<Gamma>\<close>  
| Fwd_ElimConc:  \<open>con_fwd_prop_elim e e1 e2 \<Longrightarrow> \<stileturn> [Member pos x e, (Member pos (x1) e1), (Member pos (x2) e2)]  @ \<Gamma> \<Longrightarrow>  
                 \<stileturn> [(EqAtom pos x (Conc x1 x2)), (Member pos (x1) e1), (Member pos (x2) e2)] @ \<Gamma>\<close>
(*| Bwd_PropConc:  \<open>con_bwd_prop e = es \<Longrightarrow> \<stileturn> ((\<lambda>r. [Member x e, EqAtom x (App 1 [x1,x2]), Member (x1) (fst r), Member (x2) (snd r)] @ \<Gamma>) ` es) \<Longrightarrow> 
                 \<stileturn> {[Member x e, EqAtom x (App 1 [x1,x2])] @ \<Gamma>}\<close>*)
| Order:         \<open>\<stileturn> G \<Longrightarrow> set G = set G' \<Longrightarrow> \<stileturn> G'\<close>
| Basic:         \<open>\<stileturn> [A,Neg A, G]\<close>


declare One_SC.intros [intro]

section \<open>Soundness\<close>

lemma aux_close : "Suc 0 < |rs| \<Longrightarrow>  \<Inter> (Symbolic_Regular_Algebra_Model.lang ` set rs) = {} \<Longrightarrow> \<exists>p\<in>Member pos x ` set rs . \<not> \<lbrakk>E, \<lambda>a b. a @ b\<rbrakk> p"
  apply auto
  done

lemma One_SC_soundness: \<open>\<stileturn> G \<Longrightarrow> (\<exists>p \<in> set G. \<not> \<lbrakk>E, (@)\<rbrakk> p)\<close>
proof (induct G rule: One_SC.induct)
  case (Close rs x \<Gamma>)
  then show ?case apply auto
  proof -
    assume a1:"Suc 0 < |rs|" and a2:"\<Inter> (Symbolic_Regular_Algebra_Model.lang ` set rs) = {}"
    then have "\<exists>p\<in>Member pos x ` set rs. \<not> \<lbrakk>E, (@)\<rbrakk> p" by auto
    then show "\<exists>p\<in>Member pos x ` set rs \<union> set \<Gamma>. \<not> \<lbrakk>E, (@)\<rbrakk> p" 
      by blast
  qed
next
  case (Intersect e fs x \<Gamma>)
  then show ?case  apply auto 
    by (metis INT_I eval.simps(3) image_subset_iff sup.cobounded1)
qed (auto simp:l_prod_elim is_singleton_def)

(*next
  case (Bwd_PropConc e es x1 x2 x \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def) sorry*)

definition one_sc_proof :: \<open>(char BA) form list \<Rightarrow> (char BA) form \<Rightarrow> bool\<close> where
  \<open>one_sc_proof ps p \<equiv> (\<stileturn>  Neg p # ps)\<close>

theorem sc_soundness:
  \<open>one_sc_proof ps p \<Longrightarrow> list_all \<lbrakk>E, (@)\<rbrakk> ps \<Longrightarrow> \<lbrakk>E, (@)\<rbrakk> p\<close>
  using One_SC_soundness unfolding one_sc_proof_def list_all_def
  by fastforce

section \<open>Completeness\<close>  


subsection \<open>Consistent sets\<close>

definition consistency :: "(char BA) form set set \<Rightarrow> bool" where
  "consistency C = (\<forall>S. S \<in> C \<longrightarrow> 
              (\<forall> A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
              (\<forall> A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and> 
              (\<forall> A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and> 
              (\<forall> A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and> 
              (\<forall> A. Neg (Neg A) \<in> S \<longrightarrow> S \<union> {A} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> Member neg x e \<in> S \<longrightarrow> S \<union> {Member pos x ec} \<in> C) \<and> 
              (\<forall> x y p q. EqAtom neg  x (Conc p q) \<in> S \<longrightarrow> S \<union> {EqFresh neg  x y, EqFresh pos y (Conc p q)} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> S \<union> {Member pos x e} \<in> C \<longrightarrow> S \<union> {Member pos x ec} \<in> C \<longrightarrow> S \<in> C) \<and> 
              (\<forall> x y e. Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x y, Member pos y e} \<in> C) \<and> 
              (\<forall> e1 e2 x y. regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> S \<and> EqAtom neg  x y \<in> S \<and> Member pos y e2 \<in> S \<longrightarrow> S \<union> {Member pos x e1, Member pos y e2} \<in> C) \<and>
              (\<forall> x y e. is_singleton (lang e) \<longrightarrow> Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y e} \<in> C) \<and> 
              (\<forall> x y e ec. is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> S \<and> EqAtom neg  x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y ec} \<in> C) \<and> 
              (\<forall> x rs. length rs > 1 \<longrightarrow> empty_intersection_set rs \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r) ` (set rs)) \<notin> C) \<and> 
              (\<forall> x e fs. subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> S \<and> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C) \<and> 
              (\<forall> x e fs. eq_len_intersect e fs \<longrightarrow>  S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> {Member pos x e} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x (Conc x1 x2), Member pos x1 e1, Member pos x2 e2} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos (x1) e1 \<in> S \<and> Member pos (x2) e2 \<in> S \<longrightarrow> S \<union> {EqAtom pos x (Conc x1 x2), Member pos x e, Member pos (x1) e1, Member pos (x2) e2} \<in> C) \<and> 
              (\<forall> S'. S' = S \<longrightarrow> S' \<in> C))"

definition \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> one_sc_proof S' FF\<close>


lemma UN_finite_bound:
  assumes \<open>finite A\<close> and \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

lemma split_list:
  assumes \<open>x \<in> set A\<close>
  shows \<open>set (x # removeAll x A) = set A \<and> x \<notin> set (removeAll x A)\<close>
  using assms by auto


theorem consistent:
  assumes inf_param: \<open>infinite (UNIV::'a set)\<close>
  shows \<open>consistency {S:: (char BA) form set. \<exists>G. S = set G \<and> \<not> (\<stileturn> G)}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: \<open>(char BA) form set\<close>
  assume \<open>S \<in> {set G | G. \<not> (\<stileturn> G)}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G :: \<open>(char BA) form list\<close>
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
    fix x y p q 
    assume \<open>EqAtom neg x (Conc p q) \<in> S\<close>
    then show \<open>S \<union> {EqFresh neg x y, EqFresh pos y (Conc p q)} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
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
    assume \<open>con_fwd_prop e e1 e2\<close> and \<open>EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Member pos x e # EqAtom pos x (Conc x1 x2) # Member pos x1 e1# Member pos x2 e2 # G)\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_PropConc apply auto  
      by (smt (verit, del_insts) insert_absorb list.simps(15))
    moreover have \<open>S \<union> {Member pos x e,EqAtom pos x (Conc x1 x2),Member pos x1 e1, Member pos x2 e2} = set (Member pos x e # EqAtom pos x (Conc x1 x2) # Member pos x1 e1# Member pos x2 e2 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Member pos x e, EqAtom pos x (Conc x1 x2), Member pos x1 e1, Member pos x2 e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
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
    assume \<open>con_fwd_prop_elim e e1 e2\<close> and \<open>EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then have \<open>\<not> (\<stileturn> EqAtom pos x (Conc x1 x2) # Member pos x e# Member pos x1 e1#  Member pos x2 e2 # G)\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_ElimConc apply auto 
      by (smt (verit, del_insts) insert_absorb list.set_intros(2) list.simps(15))
    moreover have \<open>S \<union> {EqAtom pos x (Conc x1 x2), Member pos x e, Member pos x1 e1,  Member pos x2 e2} = set (EqAtom pos x (Conc x1 x2) # Member pos x e# Member pos x1 e1#  Member pos x2 e2 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {EqAtom pos x (Conc x1 x2), Member pos x e, Member pos x1 e1, Member pos x2 e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using \<open>\<not> (\<stileturn> G)\<close> by auto 
  }
qed


subsection \<open>Enumerating datatypes\<close>

instance \<open>rexp\<close> :: (countable) countable
  by countable_datatype

instance \<open>tm\<close> ::  countable
  by countable_datatype

instance \<open>sign\<close> :: countable
  by countable_datatype

instance form :: (countable) countable 
  by countable_datatype
  
subsection \<open>Extension to maximal consistent set\<close>

subsection \<open>Hintikka sets and Herbrand models\<close>

text \<open>
\label{sec:hintikka}
A Hintikka set is defined as follows:
\<close>

locale hintikka = 
  fixes H :: \<open>(char BA) form set\<close>
  assumes 
  Basic: \<open>\<not> (A \<in> H \<and> Neg A \<in> H)\<close> and
  FF: \<open>FF \<notin> H\<close> and
  TT: \<open>Neg TT \<notin> H\<close> and
  NegNeg : \<open>(Neg (Neg Z) \<in> H \<longrightarrow> Z \<in> H)\<close> and 
  Con: \<open>Con A B \<in> H \<longrightarrow> A \<in> H \<and> B \<in> H\<close> and
  NDis : \<open>Neg (Dis A B) \<in> H \<longrightarrow> Neg A \<in> H \<and> Neg B \<in> H\<close> and
  Dis: \<open>Dis A B \<in> H \<longrightarrow> A \<in> H \<or> B \<in> H\<close> and
  NCon:\<open>Neg (Con A B) \<in> H \<longrightarrow> Neg A \<in> H \<or> Neg B \<in> H\<close> and
 NMember: \<open>regexp_compl e ec \<longrightarrow> Member neg x e \<in> H \<longrightarrow> Member pos x ec \<in> H\<close> and 
 NEq: \<open>EqAtom neg x (Conc x1 x2) \<in> H \<longrightarrow> EqFresh neg x y \<in> H \<and> EqFresh pos y (Conc x1 x2) \<in> H\<close> and
 Cut: \<open>regexp_compl e ec \<longrightarrow> Member pos x e \<in> H \<or> Member pos x ec \<in> H\<close> and 
 EProp: \<open>Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<and> Member pos y e \<in> H\<close> and
 NSubsume: \<open>regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> H \<and> EqAtom neg  x y \<in> H \<and> Member pos y e2 \<in> H \<longrightarrow> Member pos x e1 \<in> H \<and> Member pos y e2 \<in> H\<close> and
 EPropElim: \<open>is_singleton (lang e) \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> Member pos y e \<in> H\<close> and 
 NPropElim: \<open>is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> H \<and> EqAtom neg  x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> Member pos y ec \<in> H\<close> and 
 Close: \<open>length rs > 1 \<longrightarrow> empty_intersection_set rs \<longrightarrow> ((\<lambda>r. Member pos x r) ` (set rs)) \<subseteq> H\<close> and 
 Subsumer:    \<open>subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> H \<and> ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H \<longrightarrow> ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H\<close> and 
 Intersect:    \<open>eq_len_intersect e fs \<longrightarrow>  ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H \<longrightarrow> Member pos x e \<in> H\<close> and 
 Con_fwd_prop: \<open>con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos x1 e1 \<in> H \<and> Member pos x2 e2 \<in> H \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos x1 e1 \<in> H \<and> Member pos x2 e2 \<in> H\<close> and 
 Con_fwd_prop_elim: \<open>(con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos (x1) e1 \<in> H \<and> Member pos (x2) e2 \<in> H \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos x e \<in> H \<and> Member pos (x1) e1 \<in> H \<and> Member pos (x2) e2 \<in> H)\<close>

subsection \<open>Model existence theorem\<close>

subsection \<open>Completeness for Natural Deduction\<close>

theorem One_SC_completeness':
  fixes p :: \<open>(char BA) form\<close>
  assumes  mod: \<open>\<forall>(e :: nat \<Rightarrow> string) f. list_all (eval e f) ps \<longrightarrow> eval e f p\<close>
  shows \<open>one_sc_proof ps p\<close>
  sorry


end