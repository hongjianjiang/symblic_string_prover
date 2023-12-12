
section \<open>Sequent Calculus\<close>

theory Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Multiset"
begin

section \<open>Terms and 'u formulae\<close>

text \<open>
\label{sec:terms} The datatypes of terms and 'u formulae are defined as follows:
\<close>
type_synonym var_sym = string
type_synonym fun_sym = string
type_synonym pred_sym = string
type_synonym 'u var_denot = \<open>var_sym \<Rightarrow> 'u\<close>
type_synonym 'u fun_denot = \<open>fun_sym \<Rightarrow> 'u list \<Rightarrow> 'u\<close>
type_synonym 'u pred_denot = \<open>pred_sym \<Rightarrow> 'u list \<Rightarrow> bool\<close>

datatype fterm = Var var_sym | Fun fun_sym \<open>var_sym list\<close>

datatype 't literal = 
  is_pos : Pos (get_pred: pred_sym) (get_terms: "'t list")
  | Neg (get_pred: pred_sym) (get_terms: "'t list")

fun complement :: "'t literal \<Rightarrow> 't literal" ("_\<^sup>c" [300] 300) where
 "(Pos P ts)\<^sup>c = Neg P ts"
|"(Neg P ts)\<^sup>c = Pos P ts"

fun fnat :: "nat fun_denot" where 
  "fnat f [n,m] = (if f = ''udd'' then n + m else
                if f = ''mul'' then n * m else 0)"
| "fnat f [] = (if f = ''one'' then 1 else if f = ''zero'' then 0 else 0)"
| "fnat f us = 0"

fun enat ::"nat var_denot" where 
"enat x = (if x = ''x'' then 26 else if x = ''y'' then 5 else 0)"

fun evalt ::"'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> fterm \<Rightarrow> 'u" where 
  "evalt E F (Var x) = E x"
| "evalt E F (Fun f ts) = (F f (map E ts))"

abbreviation evalts :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> fterm list \<Rightarrow> 'u list" where 
"evalts E F ts \<equiv> map (evalt E F) ts"

fun evall ::"'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm literal \<Rightarrow> bool" where 
"evall E F \<Gamma> (Pos p ts) \<longleftrightarrow> (\<Gamma> p (evalts E F ts))" |
"evall E F \<Gamma> (Neg p ts) \<longleftrightarrow> \<not> (\<Gamma> p (evalts E F ts))"


datatype 'u form = 
    EqAtom "fterm" "fterm"                      
  | NeqAtom "fterm" "fterm" 
  | Member "fterm" "'u rexp"
  | Nmember "fterm" "'u rexp"
  | Dis "'u form" "'u form"                     
  | Con "'u form" "'u form"                      
  | Neg "'u form"     
  | FF


primrec eval :: \<open>'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> 'u form \<Rightarrow> bool\<close> where
  "eval e f (EqAtom x y) = (evalt e f x = evalt e f y)" 
| "eval e f (NeqAtom x y) = (evalt e f x \<noteq> evalt e f y)" 
| "eval e f (Member x r) = ([evalt e f x] \<in> lang r)"
| "eval e f (Nmember x r) = ([evalt e f x] \<in> (UNIV - lang r))"
| "eval e f (Dis m n) = (eval e f m \<or> eval e f n)"
| "eval e f (Con m n) = (eval e f m \<and> eval e f n)"
| "eval e f (Neg m) = (\<not> eval e f m)"
| "eval e f FF = False"


definition model :: \<open>'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow>  'u form list \<Rightarrow> 'u form \<Rightarrow> bool\<close> ("_,_,_ \<Turnstile> _" [50,50] 50) where
  \<open>(e,f,ps \<Turnstile> p) = (list_all (eval e f) ps \<longrightarrow> eval e f p)\<close>

fun pre_image_conc ::"'u rexp \<Rightarrow> ('u rexp * 'u rexp) set" where 
"pre_image_conc r = {(a,b)| a b. lang r = (lang (Times a b))}"

fun empty_intersection_set :: "'u rexp list \<Rightarrow> bool" where
  "empty_intersection_set fs = (\<Inter>(lang ` set fs) = {} \<and> length fs > 1 )"

fun subset_intersect_set :: "'u rexp \<Rightarrow> 'u rexp set \<Rightarrow> bool" where 
  "subset_intersect_set r fs = (\<Inter>(lang ` fs) \<subseteq> lang r)"

fun eq_len_intersect :: "'u rexp \<Rightarrow> 'u rexp list \<Rightarrow> bool" where 
  "eq_len_intersect r fs = (\<Inter>(lang ` set fs) = lang r \<and> length fs > 1)"


fun member_var_rexp :: "string list\<Rightarrow> 'u rexp list \<Rightarrow> 'u form set" where 
"member_var_rexp [] b = {}"|
"member_var_rexp (v # va) [] = {}"|
"member_var_rexp (x#xs) (y#ys) = (if (length xs = length ys) then insert (Member (Var x) (y)) (member_var_rexp xs (ys)) else {})"

fun con_fwd_prop ::"string \<Rightarrow> 'u rexp \<Rightarrow> 'u rexp list \<Rightarrow> bool" where
"con_fwd_prop f r es = (if f = ''concat'' then lang (r) = List.foldl (*) (lang (hd es)) (map lang (tl es)) else False)"

fun con_fwd_prop_elim ::"string \<Rightarrow> 'u rexp \<Rightarrow> 'u rexp list \<Rightarrow> bool" where
"con_fwd_prop_elim f r es = (if f = ''concat'' then lang (r) = List.foldl (*) (lang (hd es)) (map lang (tl es)) \<and> is_singleton (lang r) else False)"

fun con_bwd_prop ::"string \<Rightarrow> 'u rexp \<Rightarrow> ('u rexp * 'u rexp) set" where
"con_bwd_prop f r = (if f = ''concat'' then pre_image_conc r else {})"


value "List.foldl (*) (lang (Atom 1)) (map lang [Atom (2::nat), Atom 3])"

lemma "is_singleton (lang (Times (Atom 1) (Times (Atom 2) (Atom (3::nat)))))"
apply (simp add:is_singleton_def) apply(simp add:c_prod_def) done


abbreviation msins ("_, _" [56,56] 56) where "x,M == insert x M"

inductive One_SC :: \<open>'u form set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> 0) where
  AlphaCon:      \<open>\<turnstile> A,B,\<Gamma> \<Longrightarrow> \<turnstile> Con A B,\<Gamma>\<close>
| AlphaNegOr:    \<open>\<turnstile> Neg A, Neg B, \<Gamma> \<Longrightarrow> \<turnstile> Neg (Dis A B), \<Gamma>\<close>
| AlphaOr:       \<open>\<turnstile> A , \<Gamma> \<Longrightarrow> \<turnstile> B , \<Gamma> \<Longrightarrow> \<turnstile> Dis A B , \<Gamma>\<close>
| AlphaNegAnd:   \<open>\<turnstile> Neg A , \<Gamma> \<Longrightarrow> \<turnstile> Neg B , \<Gamma> \<Longrightarrow> \<turnstile> Neg (Con A B) , \<Gamma>\<close>
| AlphaNegNeg:   \<open>\<turnstile> A, \<Gamma> \<Longrightarrow> \<turnstile> Neg (Neg A) , \<Gamma>\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> (Member x ec) , \<Gamma> \<Longrightarrow> \<turnstile> (Nmember x e) , \<Gamma>\<close>
| NotEq:         \<open>\<turnstile> EqAtom x y , (EqAtom y (Fun f fs) , \<Gamma>) \<Longrightarrow> \<turnstile> EqAtom x (Fun f fs), \<Gamma>\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<turnstile> Member x e , \<Gamma> \<Longrightarrow> \<turnstile> Member x ec , \<Gamma> \<Longrightarrow>  \<turnstile> \<Gamma>\<close>
| EqProp:        \<open>\<turnstile> Member x e , EqAtom x y , Member y e , \<Gamma> \<Longrightarrow> \<turnstile> Member x e , EqAtom x y , \<Gamma>\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<turnstile> Member x e1 , Member y e2 , \<Gamma> \<Longrightarrow> \<turnstile> Member x e1 , NeqAtom x y , Member y e2 , \<Gamma>\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<turnstile> Member (Var x) e , Member (Var y) e , \<Gamma> \<Longrightarrow> \<turnstile> Member (Var x) e , (EqAtom (Var x) (Var y)) , \<Gamma>\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<turnstile> (Member (Var x) e) , (Member (Var y) ec) , \<Gamma> \<Longrightarrow>  \<turnstile> (Member (Var x) e) , (NeqAtom (Var x) (Var y)) , \<Gamma>\<close>
| Close:         \<open>empty_intersection_set fs \<Longrightarrow> \<turnstile> {FF} \<Longrightarrow> \<turnstile> ((\<lambda>r. Member (Var x) r) ` set fs) \<union> \<Gamma>\<close>
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<turnstile> ((\<lambda>r. Member x r) ` fs) \<union> \<Gamma> \<Longrightarrow> \<turnstile> Member x e , ((\<lambda>r. Member x r) ` fs) \<union> \<Gamma>\<close>
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<turnstile> Member (Var x) e , \<Gamma>  \<Longrightarrow>  \<turnstile> ((\<lambda>r. Member (Var x) r) ` (set fs)) \<union> \<Gamma>\<close>
| Fwd_PropConc:  \<open>con_fwd_prop f e es \<Longrightarrow> \<turnstile> (Member (Var x) e, (EqAtom (Var x) (Fun f xs), member_var_rexp xs es)) \<union> \<Gamma> \<Longrightarrow> \<turnstile> EqAtom (Var x) (Fun f xs), member_var_rexp xs es \<union> \<Gamma>\<close>
| Fwd_ElimConc:  \<open>con_fwd_prop_elim f e es \<Longrightarrow> \<turnstile> Member (Var x) e , EqAtom (Var x) (Fun f xs), member_var_rexp xs es \<union> \<Gamma> \<Longrightarrow>  \<turnstile> (EqAtom (Var x) (Fun f xs), member_var_rexp xs es) \<union> \<Gamma>\<close>
| Bwd_PropConc:  \<open>\<turnstile> Member (Var x) e , EqAtom (Var x) (Fun f xs), \<Gamma> \<Longrightarrow> \<turnstile> \<Union>((\<lambda>r. Member (Var (hd xs)) (fst r), Member (Var (hd (tl xs))) (snd r), Member (Var x) e, EqAtom (Var x) (Fun f xs), \<Gamma>) ` con_bwd_prop f e)\<close>

subsection \<open>Soundness\<close>

lemma SC_soundness: \<open>\<turnstile> \<Gamma> \<Longrightarrow>\<forall>p \<in> \<Gamma>. eval e f p\<close>
proof (induct \<Gamma> rule: One_SC.induct)
  case (AlphaCon A B \<Gamma>)
  then show ?case apply simp done
next
  case (AlphaNegOr A B \<Gamma>)
  then show ?case apply auto done
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
  then show ?case apply auto done
next
  case (NotEq x y fs \<Gamma>)
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
    by (metis is_singletonE list.inject singletonD) 
next
  case (NeqPropElim e ec x y \<Gamma> )
  then show ?case apply auto done
next
  case (Close fs x \<Gamma>)
  then show ?case apply simp  done
next
  case (Subsume e fs x \<Gamma>)
  then show ?case apply auto 
    by (smt (verit) INT_I Un_iff eval.simps(3) image_iff subsetD) 
next
  case (Intersect e fs x \<Gamma>)
  then show ?case apply auto 
    by blast
next 
  case (Fwd_PropConc fa ea es x xs \<Gamma>)
  then show ?case apply auto done
next 
  case (Fwd_ElimConc fa ea es x xs \<Gamma>)
  then show ?case apply auto done
next 
  case (Bwd_PropConc x ea fa xs \<Gamma>)
  then show ?case  apply simp sorry
qed
 


lemma cancel_comp1 : "(l\<^sup>c)\<^sup>c = l" 
  by(cases l) auto

lemma cancel_compl2: 
  assumes asm: "l1\<^sup>c = l2\<^sup>c"
  shows "l1 = l2"
proof -
  from asm have "(l1\<^sup>c)\<^sup>c = (l2\<^sup>c)\<^sup>c"
    by auto
  then have "l1 = (l2\<^sup>c)\<^sup>c" using cancel_comp1[of l1] by auto
  then show ?thesis using cancel_comp1[of l2] by auto
qed

lemma comp_exi1: "\<exists>l'. l' = l\<^sup>c"
  by(cases l) auto

lemma comp_exi2: "\<exists>l. l' = l\<^sup>c"
proof 
  show "l' = (l'\<^sup>c)\<^sup>c" using cancel_comp1[of l'] by auto
qed

lemma comp_swap: "l1\<^sup>c = l2 \<longleftrightarrow> l1 = l2\<^sup>c "
proof -
  have "l1\<^sup>c = l2 \<Longrightarrow> l1 = l2\<^sup>c"  using cancel_comp1[of l1] by auto 
  moreover 
  have "l1 = l2\<^sup>c \<Longrightarrow> l1\<^sup>c = l2" using cancel_comp1 by auto 
  ultimately 
  show ?thesis by auto
qed

subsection \<open>Completeness\<close>


end