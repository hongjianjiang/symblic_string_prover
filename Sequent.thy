
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

fun basic_solution :: "string form list \<Rightarrow> bool" where
  "basic_solution ls = (if ls = [] then False 
                       else list_all is_Member ls \<and> distinct_variable ls \<and> single_word ls)"  

lemma "basic_solution [Member (Var 1) (Pred (Atom CHR ''a'')), Member (Var 2) (Pred (Atom CHR ''b''))]"
  apply auto
   apply (simp add:distinct_variable_def single_word_def)
   apply (simp add:distinct_variable_def single_word_def)
  done


lemma "\<lbrakk>E, F\<rbrakk> (NEqAtom x y) \<Longrightarrow> \<lbrakk>E, F\<rbrakk> (EqAtom y (Fun f ls)) \<Longrightarrow> \<lbrakk>E, F\<rbrakk> (NEqAtom x (Fun f ls)) "
  apply auto
  done

definition model :: \<open>(nat \<Rightarrow> char list) \<Rightarrow> ('f \<Rightarrow> char list list \<Rightarrow> char list) \<Rightarrow> 'f form list \<Rightarrow> 'f form \<Rightarrow> bool\<close> ("_,_,_ \<Turnstile> _" [50,50] 50) where
  \<open>(E,F,ps \<Turnstile> p) = (list_all \<lbrakk>E,F\<rbrakk> ps \<longrightarrow> \<lbrakk>E, F\<rbrakk> p)\<close>

fun pre_image_conc ::"char BA rexp \<Rightarrow> (char BA rexp * char BA rexp) set" where
  "pre_image_conc r = {(a,b)|a b. lang r = (lang (Times a b))}"

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

inductive One_SC :: \<open>string form list set \<Rightarrow> bool\<close> (\<open>\<stileturn> _\<close> 0) where
  AlphaCon:      \<open>\<stileturn> {[A,B]} \<Longrightarrow> \<stileturn> {[Con A B]}\<close>
| AlphaNegOr:    \<open>\<stileturn> {Neg A #Neg B#\<Gamma>} \<Longrightarrow> \<stileturn> {Neg (Dis A B)# \<Gamma>}\<close>
| AlphaOr:       \<open>\<stileturn> {A# \<Gamma>, B# \<Gamma>} \<Longrightarrow> \<stileturn> {Dis A B # \<Gamma>}\<close>
| AlphaNegAnd:   \<open>\<stileturn> {Neg A # \<Gamma>, Neg B # \<Gamma>} \<Longrightarrow> \<stileturn> {Neg (Con A B) # \<Gamma>}\<close>
| AlphaNegNeg:   \<open>\<stileturn> {A# \<Gamma>} \<Longrightarrow> \<stileturn> {Neg (Neg A) # \<Gamma>}\<close>
| NotMember:     \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> {(Member x ec) # \<Gamma>} \<Longrightarrow> \<stileturn> {(NMember x e) # \<Gamma>}\<close>
| NotEq:         \<open>y \<notin> (params_tm x \<union> params_tm z) \<Longrightarrow>  \<stileturn> {[NEqAtom x (Var y), EqAtom (Var y) z]} \<Longrightarrow> \<stileturn> {[NEqAtom x z]}\<close>
| Cut:           \<open>regexp_compl e ec \<Longrightarrow> \<stileturn> {Member x e # \<Gamma>, Member x ec # \<Gamma>} \<Longrightarrow>  \<stileturn> {\<Gamma>}\<close>
| EqProp:        \<open>\<stileturn> {Member x e # EqAtom x y # Member y e # \<Gamma>} \<Longrightarrow> \<stileturn> {Member x e # EqAtom x y # \<Gamma>}\<close>
| NeqSubsume:    \<open>regexp_empty e1 e2 \<Longrightarrow> \<stileturn> {Member x e1 # Member y e2 # \<Gamma>} \<Longrightarrow> \<stileturn> {Member x e1 # NEqAtom x y # Member y e2 # \<Gamma>}\<close>
| EqPropElim:    \<open>is_singleton (lang e) \<Longrightarrow> \<stileturn> {Member x e # Member y e # \<Gamma>}\<Longrightarrow> \<stileturn> {Member x e # (EqAtom x y) # \<Gamma>}\<close>
| NeqPropElim:   \<open>is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow> \<stileturn> {(Member x e) # (Member y ec) # \<Gamma>} \<Longrightarrow>  
                 \<stileturn> {(Member x e) # (NEqAtom x y) # \<Gamma>}\<close>
| Close:         \<open>empty_intersection_set fs \<Longrightarrow> \<stileturn> {} \<Longrightarrow> \<stileturn> {((map (\<lambda>r. Member x r) fs)) @ \<Gamma>}\<close> 
| Subsume:       \<open>subset_intersect_set e fs \<Longrightarrow> \<stileturn> {(map (\<lambda>r. Member x r) fs) @ \<Gamma>} \<Longrightarrow> \<stileturn> {Member x e # (map (\<lambda>r. Member x r) fs) @ \<Gamma>}\<close> 
| Intersect:     \<open>eq_len_intersect e fs \<Longrightarrow> \<stileturn> {Member x e # \<Gamma>}  \<Longrightarrow>  \<stileturn> {(map (\<lambda>r. Member x r) (fs)) @ \<Gamma>}\<close> 
| Fwd_PropConc:  \<open>con_fwd_prop f e es \<Longrightarrow> \<stileturn> {(Member x e)#(EqAtom x (Fun f xs))#(member_var_rexp xs es) @ \<Gamma>} 
                 \<Longrightarrow> \<stileturn> {(EqAtom x (Fun f xs))#(member_var_rexp xs es) @ \<Gamma>}\<close>  
| Fwd_ElimConc:  \<open>con_fwd_prop_elim f e es \<Longrightarrow> \<stileturn> {Member x e # EqAtom x (Fun f xs)# member_var_rexp xs es  @ \<Gamma>} \<Longrightarrow>  
                 \<stileturn> {(EqAtom x (Fun f xs)# member_var_rexp xs es) @ \<Gamma>}\<close>
| Bwd_PropConc:  \<open>con_bwd_prop f e = es \<Longrightarrow> \<stileturn> ((\<lambda>r. Member (Var (hd xs)) (fst r)# Member (Var (hd (tl xs))) (snd r)# Member x e # EqAtom x (Fun f xs) # \<Gamma>) ` es) \<Longrightarrow> 
                 \<stileturn> {Member x e # EqAtom x (Fun f xs)# \<Gamma>}\<close>
| Order:         \<open>\<stileturn> {G} \<Longrightarrow> set G = set G' \<Longrightarrow> \<stileturn> {G'}\<close>
| Basic:         \<open>\<stileturn> {}\<close>
| Basic1:        \<open>basic_solution G \<Longrightarrow> \<stileturn> {G}\<close>

declare One_SC.intros [intro]

lemma "\<stileturn> {((map (\<lambda>r. Member x r) [Pred (Atom CHR ''b''), Pred (Atom CHR ''a'')] @ []))}"
  apply (rule Close)
  subgoal apply auto done
  apply (rule Basic) 
  done


lemma "\<stileturn> {((map (\<lambda>r. Member x r) [Pred (Atom CHR ''b''), Pred (Atom CHR ''a'')] @ []))}"
  apply (rule Close)
  apply (auto simp:distinct_variable_def single_word_def)
  done

subsection \<open>Soundness\<close>

lemma SC_soundness: 
  \<open>\<stileturn> G \<Longrightarrow> \<forall>ls \<in> G. \<exists>p \<in> set ls. \<not> \<lbrakk>E, F\<rbrakk> p\<close>
proof (induct G rule: One_SC.induct)
  case (AlphaCon A B)
  then show ?case  apply auto done
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
  case (NotEq y x z)
  then show ?case apply simp sorry
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
  then show ?case apply auto done
next
  case (NeqPropElim e ec x y \<Gamma>)
  then show ?case apply (auto simp: is_singleton_def) done 
next
  case (Close fs x \<Gamma>)
  then show ?case  by force
next
  case (Subsume e fs x \<Gamma>)
  then show ?case  by auto
next
  case (Intersect e fs x \<Gamma>)
  then show ?case  by force
next
  case (Fwd_PropConc f e es x xs \<Gamma>)
  then show ?case apply auto sorry
next
  case (Fwd_ElimConc f e es x xs \<Gamma>)
  then show ?case apply auto sorry
next
  case (Bwd_PropConc f e es xs x \<Gamma>)
  then show ?case apply auto sorry
next
  case (Order G G')
  then show ?case apply auto done
next
  case Basic
  then show ?case apply auto done
next
  case (Basic1 G)
  then show ?case apply (auto simp:single_word_def distinct_variable_def) sorry
qed


subsection \<open>Completeness\<close>

theorem SC_completeness:
  assumes \<open>\<exists>p\<in> G. \<forall>q\<in> set p. eval e f q\<close>
  shows \<open>\<stileturn> G\<close>
  sorry

end