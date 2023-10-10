theory Extend_Kleene_Algebra_Model
  imports Extend_Kleene_Algebra
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

text \<open>{\ldots} and further to regular languages. For the sake of
simplicity we just copy in the axiomatisation of regular expressions
by Krauss and Nipkow~\cite{krauss12regular}.\<close>

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

instantiation reg_lan :: (type) kleene_algebra
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
  qed

end  (* instantiation *)





end