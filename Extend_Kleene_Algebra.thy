(* Title:      From Semilattices to Dioids
   Author:     Hongjian Jiang
   Maintainer: Hongjian Jiang <hongjian.jiang at cs.rptu.de>
*)

section \<open>Dioids\<close>

theory Extend_Kleene_Algebra
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
begin

lemma dual_ex_kleene_algebra:
  "class.ex_kleene_algebra inter 0 (+) (\<odot>) 1  (\<le>) (<) star"
proof
  fix x y z :: 'a
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def order_refl star_slide_var star_unfoldl_eq)
  show "z + x \<odot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (simp add: local.dual.star_inductl_var)
  show "z + y \<odot> x \<le> y \<Longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (simp add: local.opp_mult_def local.star_inductl_var)
  qed

end (* extend kleene_algebra *)

subsection \<open>Antimirow's Axioms\<close>

text \<open>Antimirow's axiomatisations of Regular Algebra~\cite{Antimirow's}.\<close>

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

class antimirow_base = star_dioid + ab_inter_semilattice_zero + 
  fixes alp  :: "'a set" ("\<bbbP>")
  assumes A12: "\<lbrakk>(1 \<^bsup>& a = 0); (a = b \<cdot> a + c)\<rbrakk> \<Longrightarrow> a = b\<^sup>\<star> \<cdot> c"
  assumes A13: "1 \<^bsup>& (a \<cdot> b) = 1 \<^bsup>& a \<^bsup>& b"                
  assumes A14: "1 \<^bsup>& a\<^sup>\<star> = 1"
  assumes A15: "x \<in> \<bbbP> \<Longrightarrow> 1 \<^bsup>& x = 0"
  assumes A16: "x \<in> \<bbbP> \<Longrightarrow> 0 \<^bsup>& x = 0"
  assumes A22: "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> (x \<cdot> a) \<^bsup>& (y \<cdot> b) = (x \<^bsup>& y) \<cdot> (a \<^bsup>& b)"
  assumes A23: "\<lbrakk>x \<in> \<bbbP>; y \<in> \<bbbP>\<rbrakk> \<Longrightarrow> (a \<cdot> x) \<^bsup>& (b \<cdot> y) = (a \<^bsup>& b) \<cdot> (x \<^bsup>& y)"


end
