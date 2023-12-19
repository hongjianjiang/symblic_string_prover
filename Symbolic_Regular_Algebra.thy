(* Title:      Symbolic_Regular_Algebra
   Author:     Hongjian Jiang
   Maintainer: Hongjian Jiang <hongjian.jiang at cs.rptu.de>
*)

section \<open>Dioids\<close>

theory Symbolic_Regular_Algebra
imports Regular_Algebras Dioid_Models Kleene_Algebra_Models
begin

subsection \<open>Antimirow's Axioms\<close>

text \<open>Antimirow's axiomatisations of Regular Algebra~\cite{Antimirow's}.\<close>

class antimirow_base = star_dioid + ab_inter_semilattice_zero_one + 
  fixes alp :: "'a set" ("\<bbbP>")
  assumes A11: "(1 + a)\<^sup>\<star> = a\<^sup>\<star>"
  assumes A12 : "1 \<^bsup>& a \<noteq> 0 \<longleftrightarrow> (\<exists>y. a = 1 + y \<and> 1 \<^bsup>& y = 0)"
  assumes A13: "1 \<^bsup>& (x \<cdot> y) = 1 \<^bsup>& x \<^bsup>& y"
  assumes A14: "1 \<^bsup>& a\<^sup>\<star> = 1"
  assumes A15: "0 \<^bsup>& a = 0"
  assumes A16: "\<lbrakk>p \<in> \<bbbP>\<rbrakk> \<Longrightarrow> 1 \<^bsup>& p = 0"
  assumes A17: "\<lbrakk>p \<in> \<bbbP>; q \<in> \<bbbP>\<rbrakk> \<Longrightarrow> (p \<cdot> a) \<^bsup>& (q \<cdot> b)  = (p \<^bsup>& q) \<cdot> (a \<^bsup>& b)"
  assumes A18: "\<lbrakk>p \<in> \<bbbP>; q \<in> \<bbbP>\<rbrakk> \<Longrightarrow> (a \<cdot> p) \<^bsup>& (b \<cdot> q)  = (a \<^bsup>& b) \<cdot> (p \<^bsup>& q)"

class Al_algebra = antimirow_base +
  assumes S12l: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  and Al : "\<lbrakk> 1 \<^bsup>& y = 0; x = y \<cdot> x + z \<rbrakk> \<Longrightarrow> x = y\<^sup>\<star> \<cdot> z"

class Ar_algebra = antimirow_base +
  assumes S12r: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  and Ar : "\<lbrakk> 1 \<^bsup>& y = 0; x = x \<cdot> y + z \<rbrakk> \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"

class A_algebra = Al_algebra + Ar_algebra

context antimirow_base begin 

lemma inter_prod1: "1 \<^bsup>& x = 1 \<Longrightarrow> 1 \<^bsup>& y = 1 \<Longrightarrow> 1 \<^bsup>& (x \<cdot> y) = 1"
  by (simp add: local.A13)

lemma inter_prod2: "1 \<^bsup>& x = 0 \<Longrightarrow> 1 \<^bsup>& y = 0 \<Longrightarrow> 1 \<^bsup>& (x \<cdot> y) = 0"
  by (simp add: local.A13)

lemma inter_prod3: "1 \<^bsup>& x = 0 \<Longrightarrow> 1 \<^bsup>& y = 1 \<Longrightarrow> 1 \<^bsup>& (x \<cdot> y) = 0"
  by (simp add: local.A13)

lemma inter_prod4: "1 \<^bsup>& x = 1 \<Longrightarrow> 1 \<^bsup>& y = 0 \<Longrightarrow> 1 \<^bsup>& (x \<cdot> y) = 0"
  by (simp add: local.A13)

end

sublocale Al_algebra \<subseteq> dual: Ar_algebra
    "(+)" "1" "(\<odot>)"  "inter" "0" "(\<le>)" "(<)" "star" "alp"
proof 
  fix x y z p q a b
  show "x \<odot> y\<odot> z= x \<odot> (y\<odot> z)"
    by (simp add: local.mult_assoc times.opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (simp add: local.distrib_left local.opp_mult_def)
  show "1 \<odot> x = x" 
    by (simp add: local.opp_mult_def)
  show "x \<odot> 1 = x"
    by (simp add: local.opp_mult_def)
  show "0 + x = x"
    by simp
  show "0 \<odot> x = 0" 
    by (simp add: local.opp_mult_def)
  show "x \<odot> 0 = 0"
    by (simp add: local.opp_mult_def)
  show "x + x = x"
    by simp
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (simp add: local.opp_mult_def)
  show "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
    by (simp add: local.A11)
  show "(1 \<^bsup>& x \<noteq> 0) = (\<exists>y. x = 1 + y \<and> 1 \<^bsup>& y = 0)"
    by (simp add: local.A12)
  show "1 \<^bsup>& (x \<odot> y) = 1 \<^bsup>& x \<^bsup>& y"
    using local.A13 local.inter_assoc' local.inter_comm local.opp_mult_def by force
  show "1 \<^bsup>& x\<^sup>\<star> = 1"
    by (simp add: local.A14)
  show "0 \<^bsup>& x = 0"
    by simp
  show "p \<in> \<bbbP> \<Longrightarrow> 1 \<^bsup>& p = 0"
    by (simp add: local.A16)
  show "1 + x\<^sup>\<star> \<odot> x = x\<^sup>\<star>"
    by (simp add: local.S12l local.opp_mult_def)
  show "1 \<^bsup>& y = 0 \<Longrightarrow> x = x \<odot> y + z \<Longrightarrow> x = z \<odot> y\<^sup>\<star>"
    by (simp add: local.Al local.opp_mult_def)
  show "(x + y) \<^bsup>& z = x \<^bsup>& z + y \<^bsup>& z"
    by simp
  show "x \<^bsup>& (y + z) = x \<^bsup>& y + x \<^bsup>& z"
    by simp
  show "p \<in> \<bbbP> \<Longrightarrow> q \<in> \<bbbP> \<Longrightarrow> p \<odot> a \<^bsup>& (q \<odot> b) = p \<^bsup>& q \<odot> (a \<^bsup>& b)"
    by (simp add: local.A18 local.opp_mult_def)
  show "p \<in> \<bbbP> \<Longrightarrow> q \<in> \<bbbP> \<Longrightarrow> a \<odot> p \<^bsup>& (b \<odot> q) = a \<^bsup>& b \<odot> (p \<^bsup>& q)"
    by (simp add: local.A17 local.opp_mult_def)
qed

context Al_algebra
begin

lemma kozen_induct_l:
  assumes "x \<cdot> y + z \<le> y"
  shows "x\<^sup>\<star> \<cdot> z \<le> y"
proof (cases "1 \<^bsup>& x = 0")
  case True
  thus ?thesis 
    by (metis assms local.Al local.join.le_sup_iff local.join.sup.absorb2 local.mult_isol)
next
  case False
  then show ?thesis 
  proof -
    assume "1 \<^bsup>& x \<noteq> 0"
    then obtain x' where assm1: "x = 1 + x'" and assm2: "1 \<^bsup>& x' = 0"
      by (metis A12) 
    have "y = x\<^sup>\<star> \<cdot> (z + y)"
      using \<open>\<And>thesis. (\<And>x'. \<lbrakk>x = 1 + x'; 1 \<^bsup>& x' = 0\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms local.Al local.A11 local.distrib_right local.join.le_supE local.join.sup.absorb2 by fastforce
    thus ?thesis
      by (metis local.subdistl)
  qed
qed
end

context Ar_algebra
begin

lemma kozen_induct_r: 
  assumes "y \<cdot> x + z \<le> y"
  shows "z \<cdot> x\<^sup>\<star> \<le> y"
proof (cases "1 \<^bsup>& x = 0")
  case True
  then show ?thesis 
    by (metis assms local.Ar local.join.le_sup_iff local.join.sup.absorb2 local.mult_isor)
next
  case False
  then show ?thesis 
  proof -
    assume "1 \<^bsup>& x \<noteq> 0"
    then obtain x' where assm1: "x = 1 + x'" and assm2: "1 \<^bsup>& x' = 0"
      by (metis A12) 
    have "y = (z + y) \<cdot>  x\<^sup>\<star> "
      using \<open>\<And>thesis. (\<And>x'. \<lbrakk>x = 1 + x'; 1 \<^bsup>& x' = 0\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms local.Ar local.A11 local.distrib_left local.join.le_supE local.join.sup.absorb2 by fastforce
    thus ?thesis
      by (metis local.join.sup.cobounded1 local.mult_isor)
  qed
qed
end


sublocale Ar_algebra \<subseteq> K2r_algebra
  by unfold_locales (metis S12r order_refl, metis add_comm kozen_induct_r) 

sublocale Ar_algebra \<subseteq> K1r_algebra ..

sublocale Al_algebra \<subseteq> K2l_algebra
  by unfold_locales (metis S12l order_refl, metis add_comm kozen_induct_l) 

sublocale Al_algebra \<subseteq> K1l_algebra ..

sublocale A_algebra \<subseteq> ex_kleene_algebra 
  apply unfold_locales 
  subgoal for x 
    by simp
  subgoal for x y z 
    by (simp add: local.star_inductl_var)
  subgoal for x y z 
    by (simp add: local.star_inductr_var)
  done

sublocale A_algebra \<subseteq> K1_algebra ..

sublocale A_algebra \<subseteq> K2_algebra ..

sublocale antimirow_base \<subseteq> salomaa_base  plus times 1 0 less_eq less star "%x. 1 \<^bsup>& x \<noteq> 0"
  apply unfold_locales        
  apply (simp add: local.A11)
  using local.A12 
  by blast

sublocale A_algebra \<subseteq> S_algebra plus times 1 0 less_eq less star "%x. 1 \<^bsup>& x \<noteq> 0"
  apply unfold_locales        
  apply (simp add: local.A11)
  apply (simp add: local.Al)
  apply simp
  by (simp add: local.Ar)

subsection \<open>Symbolic Regular Algebra's Axioms\<close>

text \<open> Freely generated boolean algebra on a set of predicates. \<close>

datatype 'a BA = Atom1 'a | Top | Bot | Conj "'a BA" "'a BA" | Disj "'a BA" "'a BA" | Neg "'a BA"

fun denote :: "'a BA \<Rightarrow> 'a \<Rightarrow> bool" where 
"denote (Atom1 a) c = (a = c)"|
"denote Top c = True"|
"denote Bot c = False"|
"denote (Conj p q) c = (denote p c \<and> denote q c)"|
"denote (Disj p q) c = (denote p c \<or> denote q c)"|
"denote (Neg p) c = (\<not> denote p c)"

locale EBA =  bot +  top + uminus + sup + inf +
  fixes denote :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes denote_bot : "denote bot c = False"
  assumes denote_top : "denote top c = True"
  assumes denote_compl : "denote (uminus a) c = (\<not> denote a c)"
  assumes denote_inf : "denote (inf a b) c = (denote a c \<and> denote b c)"
  assumes denote_sup : "denote (sup a b) c = (denote a c \<or> denote b c)"
begin


end

class t1 = boolean_algebra + 
  fixes alp1 :: "'a BA"
  fixes sig :: 'a 
  fixes denote1 :: "'a BA \<Rightarrow> 'a \<Rightarrow> bool"
  assumes s1: "denote1 alp1 sig"
  assumes denote_bot1 : "denote1 Bot c = False"
  assumes denote_top1 : "denote1 Top c = True"
  assumes denote_compl1 : "denote1 (Neg a) c = (\<not> denote1 a c)"
  assumes denote_inf1 : "denote1 (Conjs a b) c = (denote1 a c \<and> denote1 b c)"
  assumes denote_sup1 : "denote1 (Disj a b) c = (denote1 a c \<or> denote1 b c)"
begin 

fun denote_char :: "'a BA \<Rightarrow> 'a \<Rightarrow> bool" where
"denote_char (Atom1 a) c = (a = c)"|
"denote_char Top c = True"|
"denote_char Bot c = False"|
"denote_char (Conj p q) c = (denote_char p c \<and> denote_char q c)"|
"denote_char (Disj p q) c = (denote_char p c \<or> denote_char q c)"|
"denote_char (Neg p) c = (\<not> denote_char p c)"


sublocale EBA Bot Top Neg Disj Conj denote_char 
  apply standard 
  apply auto 
  done
end


class symbolic_algebra = A_algebra + t1

end
