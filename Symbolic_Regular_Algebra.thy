theory Symbolic_Regular_Algebra
  imports Regular_Algebras
begin

subsection \<open>Antimirow's Axioms\<close>

text \<open>Antimirow's axiomatisations of Regular Algebra~\cite{Antimirow's}.\<close>

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

class antimirow_base = star_dioid + sinter_ord + boolean_algebra +
  fixes alp  :: "'a set" ("\<bbbD>")
  assumes A12: "\<lbrakk>(1 \<^bsup>& a = 0); (a = b \<cdot> a + c)\<rbrakk> \<Longrightarrow> a = b\<^sup>\<star> \<cdot> c"
  assumes A13: "1 \<^bsup>& (a \<cdot> b) = 1 \<^bsup>& a \<^bsup>& b"                
  assumes A14: "1 \<^bsup>& a\<^sup>\<star> = 1"
  assumes A15: "x \<in> \<bbbD> \<Longrightarrow> 1 \<^bsup>& x = 0"
  assumes A16: "x \<in> \<bbbD> \<Longrightarrow> 0 \<^bsup>& x = 0"
  assumes A17: "a \<^bsup>& a = a"
  assumes A18: "a \<^bsup>& b = b \<^bsup>& a"
  assumes A19: "a \<^bsup>& (b \<^bsup>& c) = a \<^bsup>& b \<^bsup>& c"
  assumes A20: "a \<^bsup>& (b + c) = a \<^bsup>& b + a \<^bsup>& c"
  assumes A21: "a + (a \<^bsup>& b) = a"
  assumes A22: "\<lbrakk>x \<in> \<bbbD>; y \<in> \<bbbD>\<rbrakk> \<Longrightarrow> (x \<cdot> a) \<^bsup>& (y \<cdot> b) = (x \<^bsup>& y) \<cdot> (a \<^bsup>& b)"
  assumes A23: "\<lbrakk>x \<in> \<bbbD>; y \<in> \<bbbD>\<rbrakk> \<Longrightarrow> (a \<cdot> x) \<^bsup>& (b \<cdot> y) = (a \<^bsup>& b) \<cdot> (x \<^bsup>& y)"
  assumes A24: "\<lbrakk>x \<in> \<bbbD>; y \<in> \<bbbD>\<rbrakk> \<Longrightarrow> x \<^bsup>& y = x \<sqinter> y"
  assumes A25: "\<lbrakk>x \<in> \<bbbD>; y \<in> \<bbbD>\<rbrakk> \<Longrightarrow> x + y = x \<squnion> y"
begin

lemma (in antimirow_base) dual_antimirow_base:
  "class.antimirow_base (minus) (uminus) (\<sqinter>) (\<le>) (<) (\<squnion>) (\<bottom>) (\<top>) (+) (\<odot>) 1 0 (star) (\<^bsup>&) (alp) " apply unfold_locales
  apply (auto simp add: opp_mult_def mult.assoc distrib_right distrib_left)
  apply (metis local.A17 local.A19 local.A20 local.A21 local.annir local.mult_1_right)
  apply (metis local.A18 local.A20 local.A21 local.add_comm)
  apply (simp add: local.A14)
  apply(simp add:local.A15)
  apply (simp add: local.A16)
  apply (simp add: local.A17)
  apply (simp add: local.A18)
  apply (simp add: local.A19)
  apply (simp add: local.A20)
  apply (simp add: local.A21)
  apply (simp add: local.A23)
  apply (simp add: local.A22)
  apply (simp add: local.A24)
  by (simp add: local.A25)

lemma antimirow_induct_r: 
  assumes "y \<cdot> x + z \<le> y"
  shows "z \<cdot> x\<^sup>\<star> \<le> y"
  by (metis local.A20 local.join.sup_ge1 local.less_eq_def)

lemma antimirow_induct_l: 
  assumes "x \<cdot> y + z \<le> y"
  shows "x\<^sup>\<star>\<cdot>z \<le> y"
  by (metis local.A20 local.join.sup_ge1 local.less_eq_def)

end







end
