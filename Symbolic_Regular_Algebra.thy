theory Symbolic_Regular_Algebra
  imports Regular_Algebras
begin

subsection \<open>Inter Semilattices\<close> 

class inter_semilattice = inter_ord +
  assumes inter_assoc' [ac_simps]: "(x \<^bsup>& y) \<^bsup>& z = x \<^bsup>& (y \<^bsup>& z)"
  and inter_comm [ac_simps] : "x \<^bsup>& y = y \<^bsup>& x"
  and inter_idem [simp]: "x \<^bsup>& x = x"
begin

lemma inter_left_comm [ac_simps]: "y \<^bsup>& (x \<^bsup>& z) = x \<^bsup>& (y \<^bsup>& z)"
  using local.inter_assoc' local.inter_comm by auto

lemma inter_left_idem [ac_simps]: "x \<^bsup>& (x \<^bsup>& y) = x \<^bsup>& y"
  unfolding inter_assoc' [symmetric] by simp

text \<open>The definition @{term "x \<le> y \<longleftrightarrow> x \<^bsup>& y = x"} of the order is
hidden in class @{class inter_ord}.\<close>

subclass order
proof
  fix x y z :: 'a
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    using local.inter_comm local.less_def local.less_eq_def by force
  show "x \<le> x"
    by (simp add: local.less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis inter_assoc' less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: local.inter_comm local.less_eq_def)
qed

text \<open>Next we show that joins are least upper bounds.\<close>

sublocale inter: semilattice_inf "(\<^bsup>&)" apply unfold_locales 
  apply (simp add: inter_left_idem local.inter_comm local.less_eq_def)
  apply (simp add: local.inter_assoc' local.less_eq_def)
  by (metis local.inter_assoc' local.less_eq_def)

text \<open>Next we prove that joins are isotone (order preserving).\<close>

lemma inter_iso: "x \<le> y \<Longrightarrow> x \<^bsup>& z \<le> y \<^bsup>& z"
  using inter.inf_mono by blast

text \<open>
  The next lemma links the definition of order as @{term "x \<le> y \<longleftrightarrow> x \<^bsup>& y = x"}
  with a perhaps more conventional one known, e.g., from arithmetics.
\<close>

lemma order_prop: "x \<le> y \<longleftrightarrow> (\<exists>z. y \<^bsup>& z = x)"
proof
  assume "x \<le> y"
  hence "x \<^bsup>& y = x"
    by (simp add: less_eq_def)
  thus "\<exists>z. y \<^bsup>& z = x" 
    using inter.inf.commute by auto
next
  assume "\<exists>z. y \<^bsup>& z = x"
  then obtain c where "y \<^bsup>& c = x"
    by auto
  hence "y \<^bsup>& c \<le> x" 
    by simp 
  thus "x \<le> y" 
    using \<open>y \<^bsup>& c = x\<close> by auto
qed

end (* inter_semilattice *)


class inter_semiring = inter_semilattice + ab_semigroup_add + 
  assumes distrib_left [simp]: "x \<^bsup>& (y + z) = (x \<^bsup>& z) + (y \<^bsup>& z)"

class near_inter_dioid = inter_semiring +
  assumes inter_idem [simp]: "x + (x \<^bsup>& y)= x"

begin

lemma inter_isol: "x \<le> y \<Longrightarrow> z \<^bsup>& x \<le> z \<^bsup>& y"
  using local.inter.inf_mono local.order_refl by presburger

lemma inter_isol_equiv_subdistl:
  "(\<forall>x y z. x \<le> y \<longrightarrow> z \<^bsup>& x \<le> z \<^bsup>& y) \<longleftrightarrow> (\<forall>x y z. z \<^bsup>& x \<le> z \<^bsup>& (x + y))"
  by (metis local.distrib_left local.inter.inf.absorb_iff2 local.inter.inf.idem local.inter_idem)

text \<open>The following lemma is relevant to propositional Hoare logic.\<close>

lemma phl_cons1: "x \<le> w \<Longrightarrow> w \<^bsup>& y \<le> y \<^bsup>& z \<Longrightarrow> x \<^bsup>& y \<le> y \<^bsup>& z"
  using local.dual_order.trans local.inter_iso by blast
end (* near_dioid *)

subsection \<open>Antimirow's Axioms\<close>

text \<open>Antimirow's axiomatisations of Regular Algebra~\cite{Antimirow's}.\<close>

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)



class antimirow_base = star_dioid + near_inter_dioid +
  fixes alp  :: "'a set" ("\<bbbP>")
  assumes A12: "\<lbrakk>(1 \<^bsup>& a = 0); (a = b \<cdot> a + c)\<rbrakk> \<Longrightarrow> a = b\<^sup>\<star> \<cdot> c"
  assumes A13: "1 \<^bsup>& (a \<cdot> b) = 1 \<^bsup>& a \<^bsup>& b"                
  assumes A14: "1 \<^bsup>& a\<^sup>\<star> = 1"
  assumes A15: "x \<in> \<bbbP> \<Longrightarrow> 1 \<^bsup>& x = 0"
  assumes A16: "x \<in> \<bbbP> \<Longrightarrow> 0 \<^bsup>& x = 0"
  assumes A22: "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> (x \<cdot> a) \<^bsup>& (y \<cdot> b) = (x \<^bsup>& y) \<cdot> (a \<^bsup>& b)"
  assumes A23: "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> (a \<cdot> x) \<^bsup>& (b \<cdot> y) = (a \<^bsup>& b) \<cdot> (x \<^bsup>& y)"


class symbolic_algebra =  antimirow_base + boolean_algebra +
  assumes AInt: "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> x \<^bsup>& y = x \<sqinter> y"
  assumes AUni: "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> x + y = x \<squnion> y"
begin

lemma (in symbolic_algebra) dual_symbolic_algebra:
  "class.symbolic_algebra (minus) (uminus) (\<sqinter>) (\<le>) (<) (\<squnion>) (\<bottom>) (\<top>) (+) (\<odot>) 1 0 (star) (\<^bsup>&) (alp) " 
  apply unfold_locales
  apply (simp add: mult_assoc times.opp_mult_def) 
  apply (metis local.distrib_left local.inter.inf.orderE local.join.sup.cobounded2 local.join.sup_absorb2)                  apply (simp add: local.distrib_left times.opp_mult_def)
  apply (simp add: local.opp_mult_def)+
  apply (metis local.add_zerol local.distrib_left local.inter.inf.idem local.inter_idem)
  apply (simp add: local.A13 local.inter.inf.commute local.inter.inf.left_commute local.opp_mult_def)
  apply (simp add: local.A14)
  apply (simp add: local.A15)
  apply (simp add: local.A16)
  apply (simp add: local.A23 local.opp_mult_def)
  apply (simp add: local.A22 local.opp_mult_def)
  apply (simp add: local.AInt)  
  by (simp add: local.AUni)

lemma symbolic_algebra_induct_r: 
  assumes "y \<cdot> x + z \<le> y"
  shows "z \<cdot> x\<^sup>\<star> \<le> y"
  by (metis local.add_0_right local.distrib_left local.inter.inf.cobounded2 local.inter.inf.idem local.join.le_bot)

lemma symbolic_algebra_induct_l: 
  assumes "x \<cdot> y + z \<le> y"
  shows "x\<^sup>\<star>\<cdot>z \<le> y"
  by (metis local.add_0_right local.distrib_left local.inter.inf.cobounded2 local.inter.inf.idem local.join.le_bot)

end



subsection \<open>Antimirow's axiom system consistent\<close>



subsection \<open>Antimirow's Rewrite Rules Systems LF\<close>

(*TODO*)



end
