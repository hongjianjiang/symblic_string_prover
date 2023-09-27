theory Dioid_Inter 
  imports Dioid
begin 

class semigroup_inter = inter +
  assumes inter_assoc [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "(a \<^bsup>& b) \<^bsup>& c = a \<^bsup>& (b \<^bsup>& c)"
begin

sublocale inter: semigroup inter
  by standard (fact inter_assoc)

end

hide_fact inter_assoc

class ab_semigroup_inter = semigroup_inter +
  assumes inter_commute [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "a \<^bsup>& b = b \<^bsup>& a"
begin

sublocale inter: abel_semigroup inter
  by standard (fact inter_commute)

declare inter.left_commute [algebra_simps, algebra_split_simps, field_simps, field_split_simps]

lemmas inter_ac = inter.assoc inter.commute inter.left_commute

end



class inter_semilattice = inter_ord +
  assumes inter_assoc [ac_simps]: "(x \<^bsup>& y) \<^bsup>& z = x \<^bsup>& (y \<^bsup>& z)"
  and inter_comm [ac_simps] : "x \<^bsup>& y = y \<^bsup>& x"
  and inter_idem [simp]: "x \<^bsup>& x = x"
begin

lemma inter_left_comm [ac_simps]: "y \<^bsup>& (x \<^bsup>& z) = x \<^bsup>& (y \<^bsup>& z)"
  using local.inter_assoc local.inter_comm by auto

lemma inter_left_idem [ac_simps]: "x \<^bsup>& (x \<^bsup>& y) = x \<^bsup>& y"
  unfolding inter_assoc [symmetric] by simp

subclass order
proof
  fix x y z :: 'a
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    using local.inter_comm local.less_def local.less_eq_def by force
  show "x \<le> x"
    by (simp add: local.less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis inter_assoc less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: local.inter_comm local.less_eq_def)
qed

sublocale inter: semilattice_inf "(\<^bsup>&)"
  apply unfold_locales 
  apply (simp add: inter_left_idem local.inter_comm local.less_eq_def)
  apply (simp add: local.inter_assoc local.less_eq_def)
  by (metis local.inter_assoc local.less_eq_def)

text \<open>Next we prove that joins are isotone (order preserving).\<close>

lemma inter_iso: "x \<le> y \<Longrightarrow> x \<^bsup>& z \<le> y \<^bsup>& z"
  using inter.inf_mono by blast

lemma order_prop1: "x \<le> y \<longleftrightarrow> (\<exists>z. x = y \<^bsup>& z)"
proof
  assume "x \<le> y"
  hence "x \<^bsup>& y = x" 
    by (simp add: less_eq_def)
  thus "\<exists>z. x = y \<^bsup>& z" 
    by (metis inter.inf.commute)
next
  assume "\<exists>z. x = y \<^bsup>& z"
  then obtain c where "x = y \<^bsup>& c"
    by auto
  hence "x \<le> y \<^bsup>& c"
    by simp
  thus "x \<le> y"
    by simp
qed

end (* inter_semilattice *)


class inter_semilattice_zero = inter_semilattice + zero +
  assumes add_zero_l [simp]: "0 \<^bsup>& x = 0"

class ab_add_semiring = ab_semigroup_add + semigroup_inter +  
  assumes distrib_right' [simp]: "x \<^bsup>& (y + z) = x \<^bsup>& y + x \<^bsup>& z"

class ab_add_pre_semiring = ab_add_semiring +
  assumes subdistl_eq: "z + z \<^bsup>& x = z"

end