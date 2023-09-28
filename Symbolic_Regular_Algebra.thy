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

class antimirow_base = star_dioid + inter_ord + boolean_algebra +
  fixes alp  :: "'a set" ("\<bbbD>")
  assumes A12: "(1 \<^bsup>& a = 0) \<and> (a = b \<cdot> a + c) \<Longrightarrow> a = b\<^sup>\<star> \<cdot> c"
  assumes A13: "1 \<^bsup>& (a \<cdot> b) = 1 \<^bsup>& a \<^bsup>& b"                
  assumes A14: "1 \<^bsup>& a\<^sup>\<star> = 1"
  assumes A15: "1 \<^bsup>& a = 0"
  assumes A16: "x \<in> \<bbbD> \<Longrightarrow> 0 \<^bsup>& x = 0"
  assumes A17: "a \<^bsup>& a = a"
  assumes A18: "a \<^bsup>& b = b \<^bsup>& a"
  assumes A19: "a \<^bsup>& (b \<^bsup>& c) = a \<^bsup>& b \<^bsup>& c"
  assumes A20: "a \<^bsup>& (b + c) = a \<^bsup>& b + a \<^bsup>& c"
  assumes A21: "a + (a \<^bsup>& b) = a"
  assumes A22: "x \<in> \<bbbD> \<and> y \<in> vs \<Longrightarrow> (x \<cdot> a) \<^bsup>& (y \<cdot> b) = (x \<^bsup>& y) \<cdot> (a \<^bsup>& b)"
  assumes A23: "x \<in> \<bbbD> \<and> y \<in> vs \<Longrightarrow> (a \<cdot> x) \<^bsup>& (b \<cdot> y) = (a \<^bsup>& b) \<cdot> (x \<^bsup>& y)"
  assumes A24: "a \<^bsup>& b = a \<sqinter> b"
  assumes A25: "a + b = a \<squnion> b"

end
