theory Extend_Kleene_Algebra_Model
  imports Extend_Kleene_Algebra Kleene_Algebra_Models
begin


instantiation set :: (monoid_mult) ex_kleene_algebra
begin

  definition inter_set_def: \<comment> \<open>the complex product\<close>
    "A \<^bsup>& B = A \<inter> B"

  instance
  proof
    fix x y z :: "'a set"
    show "x \<^bsup>& y \<^bsup>& z = x \<^bsup>& (y \<^bsup>& z)"
      by (simp add: inf_assoc inter_set_def)
    show "x \<^bsup>& y = y \<^bsup>& x"
      by (simp add: Int_commute inter_set_def)
    show "x \<^bsup>& x = x"
      by (simp add: inter_set_def)
    show "0 \<^bsup>& x = 0"
      by (simp add: inter_set_def zero_set_def)
    show "x \<^bsup>& 0 = 0"
      by (simp add: inter_set_def zero_set_def)
    show "(x + y) \<^bsup>& z = x \<^bsup>& z + y \<^bsup>& z"
      by (simp add: inf_sup_distrib2 inter_set_def plus_set_def)
    show "x \<^bsup>& (y + z) = x \<^bsup>& y + x \<^bsup>& z"
      by (simp add: boolean_algebra.conj_disj_distrib inter_set_def plus_set_def)
  qed
end (* instantiation *)

subsection \<open>Regular Languages\<close>

datatype 'a rexp =
  Zero
| One
| Sym "('a \<Rightarrow> bool)"
| Plus "'a rexp" "'a rexp"
| Times "'a rexp" "'a rexp"
| Star "'a rexp"
| Inter "'a rexp" "'a rexp"

text \<open>The interpretation map that induces regular languages as the
images of regular expressions in the set of languages has also been
adapted from there.\<close>

fun lang :: "'a rexp \<Rightarrow> 'a lan" where
  "lang Zero = 0"  \<comment> \<open>{}\<close>
| "lang One = 1"  \<comment> \<open>{[]}\<close>
| "lang (Sym f) = {[a]| a. f a}"
| "lang (Plus x y) = lang x + lang y"
| "lang (Times x y) = lang x \<cdot> lang y"
| "lang (Star x) = (lang x)\<^sup>\<star>" 
| "lang (Inter x y) = lang x \<^bsup>& lang y "
                                          
typedef 'a reg_lan = "range lang :: 'a lan set"
  by auto

setup_lifting type_definition_reg_lan

instantiation reg_lan :: (type) ex_kleene_algebra
begin

  lift_definition star_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan"
    is star
    by (metis (opaque_lifting, no_types) image_iff lang.simps(6) rangeI)

  lift_definition zero_reg_lan :: "'a reg_lan"
    is 0
    by (metis lang.simps(1) rangeI)

  lift_definition one_reg_lan :: "'a reg_lan"
    is 1
    by (metis lang.simps(2) rangeI)

  lift_definition less_eq_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> bool"
    is less_eq .

  lift_definition less_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> bool"
    is less .

  lift_definition plus_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> 'a reg_lan"
    is plus
    by (metis (opaque_lifting, no_types) image_iff lang.simps(4) rangeI)

  lift_definition times_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> 'a reg_lan"
    is times
    by (metis (opaque_lifting, no_types) image_iff lang.simps(5) rangeI)

  lift_definition inter_reg_lan :: "'a reg_lan \<Rightarrow> 'a reg_lan \<Rightarrow> 'a reg_lan"
    is inter
    using lang.simps(7) by blast

  instance
  proof
    fix x y z :: "'a reg_lan"
    show "x + y + z = x + (y + z)"
      by transfer (metis join_semilattice_class.add_assoc')
    show "x + y = y + x"
      by transfer (metis join_semilattice_class.add_comm)
    show "x \<cdot> y \<cdot> z = x \<cdot> (y \<cdot> z)"
      by transfer (metis semigroup_mult_class.mult.assoc)
    show "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
      by transfer (metis semiring_class.distrib_right)
    show "1 \<cdot> x = x"
      by transfer (metis monoid_mult_class.mult_1_left)
    show "x \<cdot> 1 = x"
      by transfer (metis monoid_mult_class.mult_1_right)
    show "0 + x = x"
      by transfer (metis join_semilattice_zero_class.add_zero_l)
    show "0 \<cdot> x = 0"
      by transfer (metis ab_near_semiring_one_zerol_class.annil)
    show "x \<cdot> 0 = 0"
      by transfer (metis ab_near_semiring_one_zero_class.annir)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by transfer (metis plus_ord_class.less_eq_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by transfer (metis plus_ord_class.less_def)
    show "x + x = x"
      by transfer (metis join_semilattice_class.add_idem)
    show "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
      by transfer (metis semiring_class.distrib_left)
    show "z \<cdot> x \<le> z \<cdot> (x + y)"
      by transfer (metis pre_dioid_class.subdistl)
    show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
      by (simp add: local.less_eq_reg_lan.rep_eq local.one_reg_lan.rep_eq local.plus_reg_lan.rep_eq local.star_reg_lan.rep_eq local.times_reg_lan.rep_eq)
    show "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
      by (simp add: left_near_kleene_algebra_class.star_inductl local.less_eq_reg_lan.rep_eq local.plus_reg_lan.rep_eq local.star_reg_lan.rep_eq local.times_reg_lan.rep_eq)
    show "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
      by (simp add: kleene_algebra_zerol_class.star_inductr local.less_eq_reg_lan.rep_eq local.plus_reg_lan.rep_eq local.star_reg_lan.rep_eq local.times_reg_lan.rep_eq)
    show "x \<^bsup>& y \<^bsup>& z = x \<^bsup>& (y \<^bsup>& z)" 
      by (metis (mono_tags, lifting) Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inject inter_assoc' inter_reg_lan.rep_eq)
    show "x \<^bsup>& y = y \<^bsup>& x"
      by (metis Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inverse inter_comm inter_reg_lan.rep_eq)
    show "x \<^bsup>& x = x"
      by (metis Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inject inter_idem inter_reg_lan.rep_eq)
    show "0 \<^bsup>& x = 0"
      by (smt (verit) Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inverse Extend_Kleene_Algebra_Model.zero_reg_lan.rep_eq inter_reg_lan.rep_eq inter_zerol)
    show "x \<^bsup>& 0 = 0"
      by (smt (verit, del_insts) Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inject \<open>0 \<^bsup>& x = 0\<close> inter_comm inter_reg_lan.rep_eq)
    show "(x + y) \<^bsup>& z = x \<^bsup>& z + y \<^bsup>& z"
      by (metis (mono_tags, lifting) Extend_Kleene_Algebra_Model.plus_reg_lan.rep_eq Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inject ex_distrib_right inter_reg_lan.rep_eq)
    show "x \<^bsup>& (y + z) = x \<^bsup>& y + x \<^bsup>& z"
      by (metis (mono_tags, lifting) Extend_Kleene_Algebra_Model.plus_reg_lan.rep_eq Extend_Kleene_Algebra_Model.reg_lan.Rep_reg_lan_inject ex_distrib_left inter_reg_lan.rep_eq)
  qed

end  (* instantiation *)


subsection \<open>Language Model of Salomaa Algebra\<close>

abbreviation w_length :: "'a list \<Rightarrow> nat" ( "|_|")
  where "|x| \<equiv> length x"

definition l_ewp :: "'a lan \<Rightarrow> bool" where
  "l_ewp X \<longleftrightarrow> {[]} \<subseteq> X"

interpretation lan_kozen: K2_algebra "(+)" "(\<cdot>)" "1 :: 'a lan" 0 "(\<subseteq>)" "(\<subset>)" "star" ..

interpretation lan_boffa: B1_algebra "(+)" "(\<cdot>)" "1 :: 'a lan" 0 "(\<subseteq>)" "(\<subset>)" "star" ..

lemma length_lang_pow_lb:
  assumes "\<forall>x\<in>X. |x| \<ge> k" "x \<in> X^n" 
  shows "|x| \<ge> k*n"
using assms proof (induct n arbitrary: x)
  case 0 thus ?case by auto
next
  case (Suc n) 
  note hyp = this
  thus ?case
  proof -
    have "x \<in> X\<^bsup>Suc n\<^esup> \<longleftrightarrow> (\<exists> y z. x = y@z \<and> y \<in> X \<and> z \<in> X\<^bsup>n\<^esup>)"
      by (simp add:c_prod_def times_list_def)
    also from hyp have "... \<longrightarrow> (\<exists> y z. x = y@z \<and> |y| \<ge> k \<and> |z| \<ge> k*n)"
      by auto
    also have "... \<longleftrightarrow> (\<exists> y z. x = y@z \<and> |y| \<ge> k \<and> |z| \<ge> k*n \<and> ( |x| = |y| + |z| ))"
      by force
    also have "... \<longleftrightarrow> (\<exists> y z. x = y@z \<and> |y| \<ge> k \<and> |z| \<ge> k*n \<and> ( |x| \<ge> (n + 1) * k ))"
      by (auto, metis add_mono mult.commute, force)
    finally show ?thesis
      by (metis Suc_eq_plus1 hyp(3) mult.commute)
  qed
qed

lemma l_prod_elim: "w\<in>X \<cdot> Y \<longleftrightarrow> (\<exists>u v. w = u@v \<and> u\<in>X \<and> v\<in>Y)"
  by (simp add: c_prod_def times_list_def)

lemma power_minor_var: 
  assumes "\<forall>w\<in>X. k\<le>|w|"
  shows "\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n*k\<le>|w|"
  using assms
  apply (auto simp add: l_prod_elim)
  using length_lang_pow_lb trans_le_add2
  by (simp add: length_lang_pow_lb trans_le_add2 mult.commute)
 
lemma power_lb: "(\<forall>w\<in>X. k\<le>|w| ) \<longrightarrow> (\<forall>w. w\<in>X\<^bsup>Suc n\<^esup> \<longrightarrow> n*k\<le>|w| )"
  by (metis power_minor_var)

lemma prod_lb: 
  "\<lbrakk> (\<forall>w\<in>X. m \<le> length w); (\<forall>w\<in>Y. n \<le> length w) \<rbrakk> \<Longrightarrow> (\<forall>w\<in>(X\<cdot>Y). (m+n) \<le> length w)"
  by (metis l_prod_elim add_le_mono length_append) 

lemma suicide_aux_l: 
  "\<lbrakk> (\<forall>w\<in>Y. 0\<le>length w); (\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n \<le> length w) \<rbrakk> \<Longrightarrow> (\<forall>w\<in>X\<^bsup>Suc n \<^esup>\<cdot> Y. n \<le> length w)"
  apply (auto simp: l_prod_elim)
  apply (drule_tac x="ua @ va" in bspec)
  apply (auto simp add: l_prod_elim)
done

lemma suicide_aux_r: 
  "\<lbrakk> (\<forall>w\<in>Y. 0\<le>length w); (\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n \<le> length w) \<rbrakk> \<Longrightarrow> (\<forall>w\<in>Y \<cdot> X\<^bsup>Suc n\<^esup>. n \<le> length w)"
  by (auto, metis (full_types) le0 plus_nat.add_0 prod_lb)

lemma word_suicide_l: 
  assumes "\<not> l_ewp X" "Y \<noteq> {}"  
  shows "(\<forall>w\<in>Y. \<exists>n. w\<notin>X\<^bsup>Suc n \<^esup>\<cdot> Y)"
proof -
  have  "\<forall>v\<in>Y. 0\<le>length v" 
    by (metis le0)
  from assms have "\<forall>v\<in>X. 1\<le>length v"
    by (simp add: l_ewp_def, metis le_0_eq length_0_conv not_less_eq_eq)
  hence "\<forall>w\<in>Y. \<exists>n. w\<notin>X\<^bsup>Suc n \<^esup>\<cdot> Y"
    by (metis nat_mult_1_right power_lb suicide_aux_l le0 Suc_n_not_le_n)
  thus ?thesis by metis
qed 

lemma word_suicide_r: 
  assumes "\<not> l_ewp X" "Y \<noteq> {}"  
  shows "(\<forall>w\<in>Y. \<exists>n. w\<notin>Y \<cdot> X\<^bsup>Suc n\<^esup>)"
proof -
  have  "\<forall>v\<in>Y. 0\<le>length v" 
    by (metis le0)
  from assms have "\<forall>v\<in>X. 1\<le>length v"
    by (simp add: l_ewp_def, metis le_0_eq length_0_conv not_less_eq_eq)
  hence "\<forall>w\<in>Y. \<exists>n. w\<notin>Y \<cdot> X\<^bsup>Suc n \<^esup>"
    by (metis nat_mult_1_right power_lb suicide_aux_r le0 Suc_n_not_le_n)
  thus ?thesis by metis
qed 

lemma word_suicide_lang_l: "\<lbrakk> \<not> l_ewp X; Y \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists> n. \<not> (Y \<le> X\<^bsup>Suc n \<^esup>\<cdot> Y)"
  by (metis Set.set_eqI empty_iff in_mono word_suicide_l)

lemma word_suicide_lang_r: "\<lbrakk> \<not> l_ewp X; Y \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists> n. \<not> (Y \<le> Y \<cdot> X\<^bsup>Suc n\<^esup>)"
  by (metis Set.set_eqI empty_iff in_mono word_suicide_r)

text \<open>These duality results cannot be relocated easily\<close>

context K1_algebra
begin

lemma power_dual_transfer [simp]: 
  "power.power (1::'a) (\<odot>) x n = x\<^bsup>n\<^esup>"
  by (induct n, simp_all, metis opp_mult_def power_commutes)

lemma aarden_aux_l:
  "y \<le> x \<cdot> y + z \<Longrightarrow> y \<le>  x\<^bsup>Suc n\<^esup> \<cdot> y + x\<^sup>\<star> \<cdot> z"
  using dual.aarden_aux[of "y" "x" "z" "n"]
  by (auto simp add:opp_mult_def)

end

lemma arden_l: 
  assumes "\<not> l_ewp y" "x = y\<cdot>x + z" 
  shows "x = y\<^sup>\<star> \<cdot> z"
proof (rule antisym)
  show one: "y\<^sup>\<star> \<cdot> z \<le> x"
    by (metis assms(2) join_semilattice_class.add_comm left_near_kleene_algebra_class.star_inductl_eq)
  show "x \<le> y\<^sup>\<star> \<cdot> z"
  proof (cases "x = 0")
    show "x = 0 \<Longrightarrow> x \<le> y\<^sup>\<star>\<cdot>z"  
      by simp
    assume assms': "x \<noteq> 0"
    have "\<And> n. x \<le> y\<^bsup>Suc n \<^esup>\<cdot> x + y\<^sup>\<star> \<cdot> z"
      by (metis assms(2) kleene_algebra_class.aarden_aux_l subsetI)
    moreover then have "\<And> w n. w \<in> x \<Longrightarrow> w \<in> y\<^bsup>Suc n \<^esup>\<cdot> x \<or> w \<in> y\<^sup>\<star> \<cdot> z"
      by (force simp: plus_set_def)
    ultimately show "x \<le> y\<^sup>\<star> \<cdot> z"
      by (metis (full_types) all_not_in_conv assms(1) subsetI word_suicide_l)
  qed
qed

lemma arden_r: 
  assumes "\<not> l_ewp y" "x = x \<cdot> y + z" 
  shows "x = z \<cdot> y\<^sup>\<star>"
proof (rule antisym)
  show one: "z \<cdot> y\<^sup>\<star> \<le> x"
    by (metis assms(2) join.sup_commute kleene_algebra_class.star_inductr_var order_refl)
  show "x \<le> z \<cdot> y\<^sup>\<star>"
  proof (cases "x = 0")
    show "x = 0 \<Longrightarrow> x \<le> z \<cdot> y\<^sup>\<star>"  
      by simp
    assume assms': "x \<noteq> 0"
    have "\<And> n. x \<le> x \<cdot> y\<^bsup>Suc n\<^esup> + z \<cdot> y\<^sup>\<star>"
      by (metis assms(2) kleene_algebra_class.aarden_aux subsetI)
    moreover then have "\<And> w n. w \<in> x \<Longrightarrow> w \<in> x \<cdot> y\<^bsup>Suc n\<^esup> \<or> w \<in> z \<cdot> y\<^sup>\<star>"
      by (force simp: plus_set_def)
    ultimately show "x \<le> z \<cdot> y\<^sup>\<star>"
      by (metis (full_types) all_not_in_conv assms(1) subsetI word_suicide_r)
  qed
qed

text \<open>The following two facts provide counterexamples to Arden's rule if the empty word property is not considered.\<close>

lemma arden_l_counter: "\<exists> (x::'a lan) (y::'a lan) (z::'a lan). x = y \<cdot> x + z \<and> x \<noteq> y\<^sup>\<star> \<cdot> z"
proof -
  have one: "(0::'a lan) + 1 \<cdot> 1 = 1"
    by (metis ab_near_semiring_one_class.mult_onel kleene_algebra_class.dual.add_zerol)
  have two: "(1::'a lan) \<noteq> 1\<^sup>\<star> \<cdot> 0"
  proof -
    have "\<exists>x\<^sub>1. (0::'a list set) \<noteq> x\<^sub>1"
      by auto
    hence "(1::'a list set) \<noteq> 0"
      by (metis kleene_algebra_class.dual.annir kleene_algebra_class.dual.mult.right_neutral)
    thus "(1::'a list set) \<noteq> 1\<^sup>\<star> \<cdot> 0"
      by simp
  qed
  show ?thesis using one and two
    by (metis kleene_algebra_class.dual.add_zerol kleene_algebra_class.dual.add_zeror)
qed

lemma arden_r_counter: "\<exists> (x::'a lan) (y::'a lan) (z::'a lan). x = x \<cdot> y + z \<and> x \<noteq> z \<cdot> y\<^sup>\<star>"
proof -
  have one: "(0::'a lan) + 1 \<cdot> 1 = 1"
    by (metis ab_near_semiring_one_class.mult_onel kleene_algebra_class.dual.add_zerol)
  have two: "(1::'a lan) \<noteq> 0 \<cdot> 1\<^sup>\<star>"
  proof -
    have "\<exists>x\<^sub>1. (0::'a list set) \<noteq> x\<^sub>1"
      by auto
    hence "(1::'a list set) \<noteq> 0"
      by (metis kleene_algebra_class.dual.annir kleene_algebra_class.dual.mult.right_neutral)
    thus "(1::'a list set) \<noteq> 0 \<cdot> 1\<^sup>\<star>"
      by simp
  qed
  show ?thesis using one and two
    by (metis kleene_algebra_class.dual.add_zerol kleene_algebra_class.dual.add_zeror)
qed

print_locale antimirow_base

interpretation lan_antimirow_base: antimirow_base inter 0 "(+)" "(\<cdot>)" "1 :: 'a lan" "(\<subseteq>)" "(\<subset>)" "star" "{}"
proof
  
qed





end