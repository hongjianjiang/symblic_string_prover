(* Title:      Symbolic_Regular_Algebra
   Author:     Hongjian Jiang
   Maintainer: Hongjian Jiang <hongjian.jiang at cs.rptu.de>
*)

section \<open>Dioids\<close>

theory Symbolic_Regular_Algebra
imports Regular_Algebras Dioid_Models Kleene_Algebra_Models
begin

class inter_semilattice = inter +
  assumes inter_assoc' [ac_simps]: "(x \<^bsup>& y) \<^bsup>& z = x \<^bsup>& (y \<^bsup>& z)"
  and inter_comm [ac_simps] : "x \<^bsup>& y = y \<^bsup>& x"
  and inter_idem [simp]: "x \<^bsup>& x = x"

class inter_semilattice_zero = inter_semilattice + zero +  
  assumes inter_zerol [simp]: "0 \<^bsup>& x = 0"
  assumes inter_zeror [simp]: "x \<^bsup>& 0 = 0"

class ab_inter_semilattice_zero = inter_semilattice_zero + ab_semigroup_add + 
  assumes ex_distrib_right [simp]: "(x + y) \<^bsup>& z = x \<^bsup>& z + y \<^bsup>& z"
  assumes ex_distrib_left [simp]: "x \<^bsup>& (y + z) = x \<^bsup>& y + x \<^bsup>& z"


class ex_kleene_algebra = kleene_algebra + ab_inter_semilattice_zero 

lemma (in ex_kleene_algebra) dual_ex_kleene_algebra: "class.ex_kleene_algebra ((+) ) ((\<odot>) ) 1 0 (\<le>) (<) star inter"
proof 
  fix x y z
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>" 
    by simp
  show "z + x \<odot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (simp add: local.dual.star_inductl_var)
  show "z + y \<odot> x \<le> y \<Longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (simp add: local.opp_mult_def local.star_inductl_var)
qed

subsection \<open>Antimirow's Axioms\<close>

text \<open>Antimirow's axiomatisations of Regular Algebra~\cite{Antimirow's}.\<close>

class antimirow_base = star_dioid + ab_inter_semilattice_zero + 
  fixes alp  :: "'a set" ("\<bbbP>")
  assumes S11: "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
  assumes EWP : "1 \<^bsup>& x \<noteq> 0 \<longleftrightarrow> (\<exists>y. x = 1 + y \<and> 1 \<^bsup>& y = 0)"
  assumes A13: "1 \<^bsup>& (a \<cdot> b) = 1 \<^bsup>& a \<^bsup>& b"                
  assumes A14: "1 \<^bsup>& a\<^sup>\<star> = 1"
  assumes A15: "\<forall>x\<in>\<bbbP>. 1 \<^bsup>& x = 0"
  assumes A16: "0 \<^bsup>& a = 0"
  assumes A22: "\<forall>x \<in> \<bbbP>. \<forall>y \<in> \<bbbP>.(x \<cdot> a) \<^bsup>& (y \<cdot> b) = (x \<^bsup>& y) \<cdot> (a \<^bsup>& b)"
  assumes A23: "\<forall>x \<in> \<bbbP>. \<forall>y \<in> \<bbbP>.(a \<cdot> x) \<^bsup>& (b \<cdot> y) = (a \<^bsup>& b) \<cdot> (x \<^bsup>& y)"

class Al_algebra = antimirow_base +
  assumes S12l: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  and Al : "\<lbrakk> 1 \<^bsup>& y = 0; x = y \<cdot> x + z \<rbrakk> \<Longrightarrow> x = y\<^sup>\<star> \<cdot> z"

class Ar_algebra = antimirow_base +
  assumes S12r: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  and Ar : "\<lbrakk> 1 \<^bsup>& y = 0; x = x \<cdot> y + z \<rbrakk> \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"

class A_algebra = Al_algebra + Ar_algebra

sublocale Al_algebra \<subseteq> dual: Ar_algebra
    "(+)" "(\<odot>)" "1" "0" "(\<le>)" "(<)" "star" "inter" "alp"
proof 
  fix x y z a b c
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
    by (simp add: local.S11)
  show "(1 \<^bsup>& x \<noteq> 0) = (\<exists>y. x = 1 + y \<and> 1 \<^bsup>& y = 0)"
    by (simp add: local.EWP)
  show "1 \<^bsup>& (x \<odot> y) = 1 \<^bsup>& x \<^bsup>& y"
    using local.A13 local.inter_assoc' local.inter_comm local.opp_mult_def by auto
  show "1 \<^bsup>& x\<^sup>\<star> = 1"
    by (simp add: local.A14)
  show "\<forall>x\<in>\<bbbP>. 1 \<^bsup>& x = 0"
    by (simp add: local.A15)
  show "0 \<^bsup>& x = 0"
    by simp
  show "\<forall>x\<in>\<bbbP>. \<forall>y\<in>\<bbbP>. x \<odot> a \<^bsup>& (y \<odot> b) = x \<^bsup>& y \<odot> (a \<^bsup>& b)"
    by (simp add: local.A23 local.opp_mult_def)
  show "\<forall>x\<in>\<bbbP>. \<forall>y\<in>\<bbbP>. a \<odot> x \<^bsup>& (b \<odot> y) = a \<^bsup>& b \<odot> (x \<^bsup>& y)"
    by (simp add: local.A22 local.opp_mult_def)
  show "1 + x\<^sup>\<star> \<odot> x = x\<^sup>\<star>"
    by (simp add: local.S12l local.opp_mult_def)
  show "1 \<^bsup>& y = 0 \<Longrightarrow> x = x \<odot> y + z \<Longrightarrow> x = z \<odot> y\<^sup>\<star>"
    by (simp add: local.Al local.opp_mult_def)
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
      by (metis EWP) 
    have "y = x\<^sup>\<star> \<cdot> (z + y)"
      using \<open>\<And>thesis. (\<And>x'. \<lbrakk>x = 1 + x'; 1 \<^bsup>& x' = 0\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms local.Al local.S11 local.distrib_right local.join.le_supE local.join.sup.absorb2 by fastforce
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
      by (metis EWP) 
    have "y = (z + y) \<cdot>  x\<^sup>\<star> "
      using \<open>\<And>thesis. (\<And>x'. \<lbrakk>x = 1 + x'; 1 \<^bsup>& x' = 0\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms local.Ar local.S11 local.distrib_left local.join.le_supE local.join.sup.absorb2 by fastforce
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

sublocale A_algebra \<subseteq> K1_algebra ..

sublocale A_algebra \<subseteq> K2_algebra ..

subsection \<open>Symbolic Regular Algebra's Axioms\<close>

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

class symbolic_algebra = A_algebra + boolean_algebra +
  assumes inf1 : "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> x \<^bsup>& y = x \<sqinter> y"
  assumes sup1 : "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> x + y = x \<squnion> y"

print_locale symbolic_algebra
text \<open>Symbolic Regular Algebra's axiomatisations of Regular Algebra~\cite{Antimirow's}.\<close>

end
