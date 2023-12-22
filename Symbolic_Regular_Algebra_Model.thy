theory Symbolic_Regular_Algebra_Model
  imports Symbolic_Regular_Algebra Kleene_Algebra_Models
begin

subsection \<open>Regular Languages\<close>

datatype (atoms: 'a) BA = Atom 'a | Top | Bot  |
                 Conj "'a BA" "'a BA"  | 
                  Disj "'a BA" "'a BA"  | Neg "'a BA"

datatype 'a rexp = 
        Zero 
      | One 
      | Pred 'a
      | Plus "'a rexp" "'a rexp"
      | Times "'a rexp" "'a rexp"
      | Star "'a rexp"
      | Inter "'a rexp" "'a rexp"
      | Negation "'a rexp"

text \<open>The interpretation map that induces regular languages as the
images of regular expressions in the set of languages has also been
adapted from there.\<close>

primrec size_of_re :: "'a rexp \<Rightarrow> nat" where
  "size_of_re Zero = 0" |
  "size_of_re One = 0" |
  "size_of_re (Pred _) = 0" |
  "size_of_re (Plus m n) = 1 + size_of_re m + size_of_re n" |
  "size_of_re (Times m n) = 1 + size_of_re m + size_of_re n" |
  "size_of_re (Star m) = 1 + size_of_re m" |
  "size_of_re (Inter m n) = 1 + size_of_re m + size_of_re n"|
  "size_of_re (Negation m) = 1 + size_of_re m"

fun denote_ba ::"'a BA \<Rightarrow> 'a \<Rightarrow> bool" where
  "denote_ba Top c = True"|
  "denote_ba Bot c = False"|
  "denote_ba (Atom a) c = (a = c)"|
  "denote_ba (Conj a b) c = (denote_ba a c \<and> denote_ba b c)"|
  "denote_ba (Disj a b) c = (denote_ba a c \<or> denote_ba b c)"|
  "denote_ba (Neg a) c = (\<not> denote_ba a c)"

interpretation denote : eba where bot = Bot and top = Top and uminus = Neg and sup = Conj and inf = Disj and denote = denote_ba
  apply unfold_locales
  apply (auto simp add: denotation.sat_denote.simps)
  done

primrec lang :: "'a BA rexp \<Rightarrow> 'a lan" where
  "lang (Zero) = 0"
| "lang (One) = 1" 
| "lang (Pred a) = {[x]|x. denote.sat_denote a x}"
| "lang (Plus x y) = lang x + lang y"
| "lang (Times x y) = lang x \<cdot> lang y"
| "lang (Star x) = (lang x)\<^sup>\<star>" 
| "lang (Inter x y)  = lang x \<^bsup>& lang y"
| "lang (Negation x) = UNIV - lang x"

fun string_to_characterClass :: "string \<Rightarrow> char BA" where
  "string_to_characterClass s = List.foldr (\<lambda>x y. Disj x y) (List.map (\<lambda>x. Atom x) s) Bot"

fun string_to_RE :: "string \<Rightarrow> char BA rexp" where
  "string_to_RE s = Pred (string_to_characterClass s)"

definition "digit = string_to_characterClass ''0123456789''"

definition "lc = string_to_characterClass ''abcdefghijklmnopqrstuvwxyz''"

definition "uc = string_to_characterClass ''ABCDEFGHIJKLMNOPQRSTUVWXYZ''"

definition "anys = Pred Top"

fun regexp_compl ::"'a BA rexp \<Rightarrow> 'a BA rexp \<Rightarrow> bool" where 
  "regexp_compl r1 r2 = (UNIV - lang r1 = lang r2)"

fun regexp_empty ::"'a BA rexp \<Rightarrow> 'a BA rexp \<Rightarrow> bool" where 
  "regexp_empty r1 r2 = (lang r1 \<inter> lang r2 = {})"

definition alpset :: "char list set set" where 
"alpset \<equiv>  (lang ` (Pred ` {digit, lc, uc}))" 

typedef reg_lan = "(range lang) :: (char list set) set"
  by auto 

setup_lifting type_definition_reg_lan

instantiation reg_lan :: ex_kleene_algebra
begin

  lift_definition zero_reg_lan :: "reg_lan"
    is 0
    using lang.simps(1) by blast

  lift_definition one_reg_lan :: "reg_lan"
    is 1 
    using lang.simps(2) by blast

  lift_definition less_eq_reg_lan :: "reg_lan \<Rightarrow> reg_lan \<Rightarrow> bool"
    is less_eq .

  lift_definition less_reg_lan :: "reg_lan \<Rightarrow> reg_lan \<Rightarrow> bool"
    is less .

  lift_definition plus_reg_lan :: "reg_lan \<Rightarrow> reg_lan \<Rightarrow> reg_lan"
    is plus
    using lang.simps(4) by blast

  lift_definition times_reg_lan :: "reg_lan \<Rightarrow> reg_lan \<Rightarrow> reg_lan"
    is times
    using lang.simps(5) by blast

  lift_definition star_reg_lan :: "reg_lan \<Rightarrow> reg_lan"
    is star
    using lang.simps(6) by blast

  lift_definition inter_reg_lan :: "reg_lan \<Rightarrow> reg_lan \<Rightarrow> reg_lan"
    is inter
    using lang.simps(7) by blast

  instance
  proof
    fix x y z :: "reg_lan"
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
      by (simp add: less_eq_reg_lan.rep_eq one_reg_lan.rep_eq plus_reg_lan.rep_eq star_reg_lan.rep_eq times_reg_lan.rep_eq)
    show "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
      by (simp add: left_near_kleene_algebra_class.star_inductl less_eq_reg_lan.rep_eq plus_reg_lan.rep_eq star_reg_lan.rep_eq times_reg_lan.rep_eq)
    show "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
      by (simp add: kleene_algebra_zerol_class.star_inductr less_eq_reg_lan.rep_eq plus_reg_lan.rep_eq star_reg_lan.rep_eq times_reg_lan.rep_eq)
    show "x \<^bsup>& y \<^bsup>& z = x \<^bsup>& (y \<^bsup>& z)" 
      by (metis (mono_tags, lifting) Rep_reg_lan_inject inter_assoc' inter_reg_lan.rep_eq)
    show "x \<^bsup>& y = y \<^bsup>& x"
      by (metis Rep_reg_lan_inverse inter_comm inter_reg_lan.rep_eq)
    show "x \<^bsup>& x = x"
      by (metis Rep_reg_lan_inject inter_idem inter_reg_lan.rep_eq)
    show "0 \<^bsup>& x = 0"
      thm inter_reg_lan.rep_eq
      by (smt (verit) Rep_reg_lan_inverse zero_reg_lan.rep_eq inter_reg_lan.rep_eq inter_zerol)
    show "x \<^bsup>& 0 = 0"
      by (smt (verit, del_insts) Rep_reg_lan_inject \<open>0 \<^bsup>& x = 0\<close> inter_comm inter_reg_lan.rep_eq)
    show "(x + y) \<^bsup>& z = x \<^bsup>& z + y \<^bsup>& z"
      by (metis (mono_tags, lifting) plus_reg_lan.rep_eq Rep_reg_lan_inject ex_distrib_right inter_reg_lan.rep_eq)
    show "x \<^bsup>& (y + z) = x \<^bsup>& y + x \<^bsup>& z"
      by (metis (mono_tags, lifting) plus_reg_lan.rep_eq Rep_reg_lan_inject ex_distrib_left inter_reg_lan.rep_eq)
  qed
end  (* instantiation *)

subsection \<open>Language Model of Antimirow Algebra\<close>

abbreviation w_length :: "'a list \<Rightarrow> nat" ( "|_|")
  where "|x| \<equiv> length x"

definition l_ewp :: "'a lan \<Rightarrow> bool" where
  "l_ewp X \<longleftrightarrow> {[]} \<subseteq> X"

lemma inter_empty:"l_ewp X \<Longrightarrow> 1 \<^bsup>& X \<noteq> 0"
  by (simp add:l_ewp_def inter_set_def one_list_def one_set_def zero_set_def) 

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

lemma l_prod_elim: "w \<in> X \<cdot> Y \<longleftrightarrow> (\<exists>u v. w = u@v \<and> u\<in>X \<and> v\<in>Y)"
  by (simp add: c_prod_def times_list_def)

lemma power_minor_var: 
  assumes "\<forall>w\<in>X. k\<le>|w|"
  shows "\<forall>w\<in>X\<^bsup>Suc n\<^esup>. n*k\<le>|w|"
  using assms
  apply (auto simp add: l_prod_elim)
  using length_lang_pow_lb trans_le_add2
  by (simp add: length_lang_pow_lb trans_le_add2 mult.commute)
 
lemma power_lb: "(\<forall>w \<in> X. k \<le> |w| ) \<longrightarrow> (\<forall>w. w \<in> X\<^bsup>Suc n\<^esup> \<longrightarrow> n*k\<le>|w| )"
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

interpretation lan_antimirow_l: Al_algebra "(+)" "1 :: char lan" "(\<cdot>)" "(\<^bsup>&)" "0"  "(\<subseteq>)" "(\<subset>)" "star" "lang ` {Pred digit, Pred uc, Pred lc}" 
proof
  fix x y z:: "'a lan"
  show "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by simp
  show "1 \<^bsup>& y = 0 \<Longrightarrow> x = y \<cdot> x + z \<Longrightarrow> x = y\<^sup>\<star> \<cdot> z"
    using arden_l inter_empty by blast
  show "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
    by simp
  show "(1 \<^bsup>& x \<noteq> 0) = (\<exists>y. x = 1 + y \<and> 1 \<^bsup>& y = 0)"
    apply(simp add: one_set_def one_list_def inter_set_def zero_set_def plus_set_def)
    by (meson Set.set_insert insertCI)
  show "1 \<^bsup>& (x \<cdot> y) = 1 \<^bsup>& x \<^bsup>& y"
    by (auto simp: one_set_def one_list_def inter_set_def zero_set_def plus_set_def l_prod_elim )
  show "1 \<^bsup>& x\<^sup>\<star> = 1"
    apply(simp add: one_set_def one_list_def inter_set_def zero_set_def plus_set_def)
    by (metis Collect_conv_if insert_subset left_near_kleene_algebra_class.star_ref one_list_def one_set_def)
  show "0 \<^bsup>& x = 0"
    by simp
next 
  fix p :: "char list set" and x :: "nat lan"
  show "p \<in> lang ` {Pred digit, Pred uc, Pred lc} \<Longrightarrow> 1 \<^bsup>& p = 0"
    apply (simp add:one_set_def inter_set_def one_list_def zero_set_def) 
    apply (erule disjE) apply simp apply (erule disjE) apply simp apply simp done
    
next 
  fix p q :: "char list set" and x y z a b :: "char lan"
  show "p \<in> Symbolic_Regular_Algebra_Model.lang ` {Pred digit, Pred uc, Pred lc} \<Longrightarrow>
       q \<in> Symbolic_Regular_Algebra_Model.lang ` {Pred digit, Pred uc, Pred lc} \<Longrightarrow> p \<cdot> a \<^bsup>& (q \<cdot> b) = p \<^bsup>& q \<cdot> (a \<^bsup>& b)"
    apply(simp add:c_prod_def inter_set_def times_list_def) 
    apply(erule disjE) 
    subgoal apply(erule disjE) 
       apply (smt (verit, ccfv_threshold) Collect_cong append_Cons list.inject mem_Collect_eq same_append_eq)
      apply (erule disjE) apply simp 
       apply (smt (verit, ccfv_SIG) Collect_cong append_Cons append_self_conv2 list.inject)
      apply simp
      by (smt (verit, ccfv_threshold) Collect_cong append_Cons append_self_conv2 list.inject)
    subgoal apply(erule disjE) 
      apply (erule disjE) apply simp 
        apply (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject)
      apply simp        apply (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject)
      apply(erule disjE) apply (erule disjE) apply simp   apply (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject)
      apply simp        apply (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject)
      apply(erule disjE) apply simp        apply (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject)
      apply simp        apply (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject)
      done 
    done
  show "p \<in> Symbolic_Regular_Algebra_Model.lang ` {Pred digit, Pred uc, Pred lc} \<Longrightarrow>
       q \<in> Symbolic_Regular_Algebra_Model.lang ` {Pred digit, Pred uc, Pred lc} \<Longrightarrow> a \<cdot> p \<^bsup>& (b \<cdot> q) = a \<^bsup>& b \<cdot> (p \<^bsup>& q)"
    apply(simp add:c_prod_def inter_set_def times_list_def) apply auto
    done
qed

interpretation lan_antimirow_r: Ar_algebra"(+)" "1 :: char lan" "(\<cdot>)" "(\<^bsup>&)" "0"   "(\<subseteq>)" "(\<subset>)" "star" "lang ` {Pred digit, Pred uc, Pred lc}" 
proof
  fix x y z :: "char lan"
  show "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
    by (metis kleene_algebra_class.star_unfoldr_eq)
  show "1 \<^bsup>& y = 0 \<Longrightarrow> x = x \<cdot> y + z \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"
    using arden_r inter_empty by blast
qed


subsection \<open>Regular Language Model of Antimirow Algebra\<close>

notation
  Pred ("\<langle>_\<rangle>") and
  Plus (infixl "+\<^sub>r" 65) and
  Times (infixl "\<cdot>\<^sub>r" 70) and
  Inter (infixl "&\<^sub>r" 70) and
  Star ("_\<^sup>\<star>\<^sub>r" [101] 100) and
  Zero ("0\<^sub>r") and
  One ("1\<^sub>r")

primrec rexp_ewp :: "'a BA rexp \<Rightarrow> bool" where
  "rexp_ewp 0\<^sub>r = False" |
  "rexp_ewp 1\<^sub>r = True" |
  "rexp_ewp (s +\<^sub>r t) = (rexp_ewp s \<or> rexp_ewp t)" |
  "rexp_ewp (s \<cdot>\<^sub>r t) = (rexp_ewp s \<and> rexp_ewp t)" |
  "rexp_ewp (s &\<^sub>r t) = (rexp_ewp s \<and> rexp_ewp t)" |
  "rexp_ewp (s\<^sup>\<star>\<^sub>r) = True"| 
  "rexp_ewp (Pred a) = False"|
  "rexp_ewp (Negation a) = (\<not> rexp_ewp a)"

abbreviation "ro(s) \<equiv> (if (rexp_ewp s) then 1\<^sub>r else 0\<^sub>r)"

lift_definition r_ewp :: "reg_lan \<Rightarrow> bool" is "l_ewp" .

lift_definition r_lang :: "char BA rexp \<Rightarrow> reg_lan"  is "\<lambda>x. lang x"
  by (simp)

abbreviation r_sim :: "char BA rexp \<Rightarrow> char BA rexp \<Rightarrow> bool" (infix "\<sim>" 50) where
  "p \<sim> q \<equiv> r_lang p = r_lang q"

declare Rep_reg_lan [simp]
declare Rep_reg_lan_inverse [simp]
declare Abs_reg_lan_inverse [simp]

lemma rexp_ewp_l_ewp: "l_ewp (lang x) = rexp_ewp x"
proof (induct x)
  case (Star x) thus ?case
  proof -
    have "1 = insert (1::'a list) 0"
      by (simp add: one_set_def)
    then show ?thesis
      by (simp add: l_ewp_def one_list_def zero_set_def)
  qed
qed (simp_all add:l_ewp_def zero_set_def one_set_def one_list_def plus_set_def c_prod_def times_list_def inter_set_def)

theorem regexp_ewp:
  defines P_def: "P(t) \<equiv> \<exists> t'. t \<sim> ro(t) +\<^sub>r t' \<and> ro(t') = 0\<^sub>r"
  shows "P t"
proof (induct t)
  show "P(0\<^sub>r)"
    by (simp add:P_def r_lang_def, rule_tac x="0\<^sub>r" in exI, simp)
next
  show "P(1\<^sub>r)"
    by (simp add:P_def r_lang_def, rule_tac x="0\<^sub>r" in exI, simp)
next
  fix t1 t2
  assume "P(t1)" "P(t2)"
  then obtain t1' t2' 
    where "t1 \<sim> ro(t1) +\<^sub>r t1'" "ro(t1') = 0\<^sub>r"
          "t2 \<sim> ro(t2) +\<^sub>r t2'" "ro(t2') = 0\<^sub>r"
    by (metis assms rexp.distinct(1))
  thus "P(t1 +\<^sub>r t2)"
    apply (subst P_def, transfer)
    apply (rule_tac x="t1' +\<^sub>r t2'" in exI)
    apply clarsimp
    by (metis (no_types, lifting) add.left_commute join.sup_assoc join.sup_left_idem rexp.distinct(2))
 next
  fix t1 t2
  assume "P(t1)" "P(t2)"
  then obtain t1' t2' 
    where t1: "t1 \<sim> ro(t1) +\<^sub>r t1'" "ro(t1') = 0\<^sub>r" and
          t2: "t2 \<sim> ro(t2) +\<^sub>r t2'" "ro(t2') = 0\<^sub>r"
      by (metis assms rexp.distinct(1))
  thus "P(t1 \<cdot>\<^sub>r t2)"
  proof -
    let ?t' = "ro(t1) \<cdot>\<^sub>r t2' +\<^sub>r t1' \<cdot>\<^sub>r ro(t2) +\<^sub>r t1' \<cdot>\<^sub>r t2'"
    from t1 t2 have r1: "ro(?t') = 0\<^sub>r"
      by (auto)
    from t1 t2 have "t1 \<cdot>\<^sub>r t2 \<sim> (ro(t1) +\<^sub>r t1') \<cdot>\<^sub>r (ro(t2) +\<^sub>r t2')" (is "?l \<sim> ?r")
      by (transfer, simp)
    also have "?r \<sim> ro(t1) \<cdot>\<^sub>r ro(t2) +\<^sub>r ro(t1) \<cdot>\<^sub>r t2' +\<^sub>r t1' \<cdot>\<^sub>r ro(t2) +\<^sub>r t1' \<cdot>\<^sub>r t2'" (is "?l \<sim> ?r")
      apply (transfer, unfold lang.simps)
      apply (simp only: distrib_right' semiring_class.distrib_left)
      apply (metis (opaque_lifting, no_types) join_semilattice_class.add_comm semiring_class.combine_common_factor)
    done
    also have "?r \<sim> ro(t1 \<cdot>\<^sub>r t2) +\<^sub>r ro(t1) \<cdot>\<^sub>r t2' +\<^sub>r t1' \<cdot>\<^sub>r ro(t2) +\<^sub>r t1' \<cdot>\<^sub>r t2'" (is "?l \<sim> ?r")
      by (transfer, simp)
    also have "?r \<sim> ro(t1 \<cdot>\<^sub>r t2) +\<^sub>r ?t'"
      apply (transfer, unfold lang.simps)
      apply (metis (mono_tags) join_semilattice_class.add_assoc')
    done
    finally show ?thesis using r1
      apply (unfold P_def)
      apply (rule_tac x="?t'" in exI, simp)
    done
  qed
next 
  fix t1 t2
  assume "P(t1)" "P(t2)"
  then obtain t1' t2' 
    where t1: "t1 \<sim> ro(t1) +\<^sub>r t1'" "ro(t1') = 0\<^sub>r" and
          t2: "t2 \<sim> ro(t2) +\<^sub>r t2'" "ro(t2') = 0\<^sub>r"
      by (metis assms rexp.distinct(1))
  thus "P(t1 &\<^sub>r t2)"
  proof -
    let ?t' = "ro(t1) &\<^sub>r t2' +\<^sub>r t1' &\<^sub>r ro(t2) +\<^sub>r t1' &\<^sub>r t2'"
    from t1 t2 have r1: "ro(?t') = 0\<^sub>r"
      by (auto)
    from t1 t2 have "t1 &\<^sub>r t2 \<sim> (ro(t1) +\<^sub>r t1') &\<^sub>r (ro(t2) +\<^sub>r t2')" (is "?l \<sim> ?r")
      by (transfer, simp)
    also have "?r \<sim> ro(t1) &\<^sub>r ro(t2) +\<^sub>r ro(t1) &\<^sub>r t2' +\<^sub>r t1' &\<^sub>r ro(t2) +\<^sub>r t1' &\<^sub>r t2'" (is "?l \<sim> ?r")
      apply (transfer, unfold lang.simps)
      by (smt (verit, best) ex_distrib_left ex_distrib_right join.sup_assoc)
    also have "?r \<sim> ro(t1 &\<^sub>r t2) +\<^sub>r ro(t1) &\<^sub>r t2' +\<^sub>r t1' &\<^sub>r ro(t2) +\<^sub>r t1' &\<^sub>r t2'" (is "?l \<sim> ?r")
      by (transfer, simp)
    also have "?r \<sim> ro(t1 &\<^sub>r t2) +\<^sub>r ?t'"
      apply (transfer, unfold lang.simps)
      apply (metis (mono_tags) join_semilattice_class.add_assoc')
    done
    finally show ?thesis using r1
      apply (unfold P_def)
      apply (rule_tac x="?t'" in exI, simp)
    done
  qed
next
  fix s
  assume assm:"P s"
  then obtain s' where r1: "s \<sim> ro(s) +\<^sub>r s'" "ro(s') = 0\<^sub>r"
    by (metis assms rexp.distinct(1))
  thus "P (s\<^sup>\<star>\<^sub>r)"
  proof -
    let ?t' = "s' \<cdot>\<^sub>r (s')\<^sup>\<star>\<^sub>r"
    have r2: "ro(?t') = 0\<^sub>r"
      using r1(2) by auto
    from assm r1 have "(ro(s) +\<^sub>r s')\<^sup>\<star>\<^sub>r \<sim> (s')\<^sup>\<star>\<^sub>r" (is "?l \<sim> ?r")
      by (transfer, auto)
    also have "?r \<sim> 1\<^sub>r +\<^sub>r s' \<cdot>\<^sub>r (s')\<^sup>\<star>\<^sub>r" (is "?l \<sim> ?r")
      by (transfer, auto)
    also have "?r \<sim> ro(s\<^sup>\<star>\<^sub>r) +\<^sub>r ?t'"
      by simp
    finally show ?thesis
      by (metis Symbolic_Regular_Algebra_Model.lang.simps(6) assms r1(1) r2 r_lang.abs_eq r_lang.rep_eq)
  qed
next 
  fix x 
  show "P (Pred x)"
    apply (simp add:P_def r_lang_def)
    using rexp_ewp.simps(7) by fastforce
next 
  fix x 
  assume assm:"P x"
  thus "P (Negation x)"
    sorry
qed

lemma "{x|x. x = a \<or> x = b} \<in> range lang \<Longrightarrow> ({x|x. x = a} \<union> {x|x. x = b}) \<in> range lang"
  apply simp
  using Collect_cong Collect_disj_eq by auto

lemma t1:"{[x]|x. a = x} \<in> range lang"
  using lang.simps(3)[of "Atom a"]
  by (smt (verit) Collect_cong UNIV_I denote.sat_denote.elims(2) denote.sat_denote.elims(3) denote_ba.simps(3) image_iff)

lemma alp_lem_digit:"{[x] |x. denote_ba digit x} \<in> range Symbolic_Regular_Algebra_Model.lang"
  apply(simp add:digit_def)
proof -
  have c1:"{[x] |x. CHR ''0'' = x}  \<union> {[x] |x. CHR ''1'' = x} \<union> {[x] |x. CHR ''2'' = x} \<union> {[x] |x. CHR ''3'' = x} \<union> {[x] |x. CHR ''4'' = x}  \<union> {[x] |x. CHR ''5'' = x} \<union> {[x] |x. CHR ''6'' = x}  \<union> {[x] |x. CHR ''7'' = x} \<union> {[x] |x. CHR ''8'' = x}  \<union> {[x] |x. CHR ''9'' = x} = {[x] |x. CHR ''0'' = x \<or> CHR ''1'' = x \<or> CHR ''2'' = x \<or> CHR ''3'' = x \<or> CHR ''4'' = x \<or> CHR ''5'' = x \<or> CHR ''6'' = x \<or> CHR ''7'' = x \<or> CHR ''8'' = x \<or> CHR ''9'' = x}"
    apply auto done
  have c2:"{[x] |x. CHR ''0'' = x} : range lang"
    using t1 by fastforce
  have c3:"{[x] |x. CHR ''1'' = x} : range lang"
    using t1 by fastforce
  have c4:"{[x] |x. CHR ''2'' = x} : range lang"
    using t1 by fastforce
  have c5:"{[x] |x. CHR ''3'' = x} : range lang"
  using t1 by fastforce
  have c6:"{[x] |x. CHR ''4'' = x} : range lang"
    using t1 by fastforce
  have c7:"{[x] |x. CHR ''5'' = x} : range lang"
    using t1 by fastforce
  have c8:"{[x] |x. CHR ''6'' = x} : range lang"
    using t1 by fastforce
  have c9:"{[x] |x. CHR ''7'' = x} : range lang"
    using t1 by fastforce
 have c10:"{[x] |x. CHR ''8'' = x} : range lang"
   using t1 by fastforce
 have c11:"{[x] |x. CHR ''9'' = x} : range lang"
    using t1 by fastforce
  have "{[x] |x. CHR ''0'' = x}  \<union> {[x] |x. CHR ''1'' = x} \<union> {[x] |x. CHR ''2'' = x} \<union> {[x] |x. CHR ''3'' = x} \<union> {[x] |x. CHR ''4'' = x}  \<union> {[x] |x. CHR ''5'' = x} \<union> {[x] |x. CHR ''6'' = x}  \<union> {[x] |x. CHR ''7'' = x} \<union> {[x] |x. CHR ''8'' = x}  \<union> {[x] |x. CHR ''9'' = x} : range lang"
    using c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 lang.simps(4)
    apply (simp  add: image_iff plus_set_def rangeI)  
    by (metis Symbolic_Regular_Algebra_Model.lang.simps(4) insert_is_Un plus_set_def)
  then show "{[x] |x. CHR ''0'' = x \<or> CHR ''1'' = x \<or> CHR ''2'' = x \<or> CHR ''3'' = x \<or> CHR ''4'' = x \<or> CHR ''5'' = x \<or> CHR ''6'' = x \<or> CHR ''7'' = x \<or> CHR ''8'' = x \<or> CHR ''9'' = x}
    \<in> range Symbolic_Regular_Algebra_Model.lang" using c1 
    by auto 
qed

lemma alp_lem_lc:"{[x] |x. denote_ba lc x} \<in> range Symbolic_Regular_Algebra_Model.lang"
  apply(simp add:lc_def)
proof -
  have c1:"{[x] |x. CHR ''a'' = x}  \<union> {[x] |x. CHR ''b'' = x} \<union> {[x] |x. CHR ''c'' = x} \<union> {[x] |x. CHR ''d'' = x} \<union> {[x] |x. CHR ''e'' = x}  \<union> {[x] |x. CHR ''f'' = x} \<union> {[x] |x. CHR ''g'' = x}  \<union> 
           {[x] |x. CHR ''h'' = x} \<union> {[x] |x. CHR ''i'' = x}  \<union> {[x] |x. CHR ''j'' = x} \<union> {[x] |x. CHR ''k'' = x} \<union> {[x] |x. CHR ''l'' = x}  \<union> {[x] |x. CHR ''m'' = x} \<union> {[x] |x. CHR ''n'' = x}  \<union> 
           {[x] |x. CHR ''o'' = x} \<union> {[x] |x. CHR ''p'' = x}  \<union> {[x] |x. CHR ''q'' = x} \<union> {[x] |x. CHR ''r'' = x} \<union> {[x] |x. CHR ''s'' = x}  \<union> {[x] |x. CHR ''t'' = x} \<union> {[x] |x. CHR ''u'' = x}  \<union> 
           {[x] |x. CHR ''v'' = x} \<union> {[x] |x. CHR ''w'' = x}  \<union> {[x] |x. CHR ''x'' = x} \<union> {[x] |x. CHR ''y'' = x} \<union> {[x] |x. CHR ''z'' = x} 
      =  {[x] |x.
     CHR ''a'' = x \<or>
     CHR ''b'' = x \<or>
     CHR ''c'' = x \<or>
     CHR ''d'' = x \<or>
     CHR ''e'' = x \<or>
     CHR ''f'' = x \<or>
     CHR ''g'' = x \<or>
     CHR ''h'' = x \<or>
     CHR ''i'' = x \<or>
     CHR ''j'' = x \<or>
     CHR ''k'' = x \<or>
     CHR ''l'' = x \<or>
     CHR ''m'' = x \<or>
     CHR ''n'' = x \<or>
     CHR ''o'' = x \<or> CHR ''p'' = x \<or> CHR ''q'' = x \<or> CHR ''r'' = x \<or> CHR ''s'' = x \<or> CHR ''t'' = x \<or> CHR ''u'' = x \<or> CHR ''v'' = x \<or> CHR ''w'' = x \<or> CHR ''x'' = x \<or> CHR ''y'' = x \<or> CHR ''z'' = x}"
    by fastforce 
  have 2:"{[x] |x. CHR ''a'' = x} : range lang"
    using t1 by fastforce
  moreover have 3: "{[x] |x. CHR ''b'' = x} : range lang"
    using t1 by fastforce
  moreover have 4:"{[x] |x. CHR ''c'' = x} : range lang"
    using t1 by fastforce
  moreover have 5:"{[x] |x. CHR ''d'' = x} : range lang"
    using t1 by fastforce
  moreover have 6:"{[x] |x. CHR ''e'' = x} : range lang"
    using t1 by fastforce
  moreover have 7:"{[x] |x. CHR ''f'' = x} : range lang"
    using t1 by fastforce
  moreover have 8:"{[x] |x. CHR ''g'' = x} : range lang"
    using t1 by fastforce  
  moreover have 9:"{[x] |x. CHR ''h'' = x} : range lang"
    using t1 by fastforce
  moreover have 10:"{[x] |x. CHR ''i'' = x} : range lang"
    using t1 by fastforce
  moreover have 11:"{[x] |x. CHR ''j'' = x} : range lang"
    using t1 by fastforce
  moreover have 12:"{[x] |x. CHR ''k'' = x} : range lang"
    using t1 by fastforce
  moreover have 13:"{[x] |x. CHR ''l'' = x} : range lang"
    using t1 by fastforce
  moreover have 14:"{[x] |x. CHR ''m'' = x} : range lang"
    using t1 by fastforce
  moreover have 15:"{[x] |x. CHR ''n'' = x} : range lang"
    using t1 by fastforce
  moreover have 16:"{[x] |x. CHR ''o'' = x} : range lang"
    using t1 by fastforce
  moreover have 17:"{[x] |x. CHR ''p'' = x} : range lang"
    using t1 by fastforce
  moreover have 18:"{[x] |x. CHR ''q'' = x} : range lang"
    using t1 by fastforce
  moreover have 19:"{[x] |x. CHR ''r'' = x} : range lang"
    using t1 by fastforce
  moreover have 20:"{[x] |x. CHR ''s'' = x} : range lang"
    using t1 by fastforce
  moreover have 21:"{[x] |x. CHR ''t'' = x} : range lang"
    using t1 by fastforce
  moreover have 22:"{[x] |x. CHR ''u'' = x} : range lang"
    using t1 by fastforce
  moreover have 23:"{[x] |x. CHR ''v'' = x} : range lang"
    using t1 by fastforce
  moreover have 24:"{[x] |x. CHR ''w'' = x} : range lang"
    using t1 by fastforce
  moreover have 25:"{[x] |x. CHR ''x'' = x} : range lang"
    using t1 by fastforce
  moreover have 26:"{[x] |x. CHR ''y'' = x} : range lang"
    using t1 by fastforce
  moreover have 27:"{[x] |x. CHR ''z'' = x} : range lang"
    using t1 by fastforce
  have "{[x] |x. CHR ''a'' = x}  \<union> {[x] |x. CHR ''b'' = x} \<union> {[x] |x. CHR ''c'' = x} \<union> {[x] |x. CHR ''d'' = x} \<union> {[x] |x. CHR ''e'' = x}  \<union> {[x] |x. CHR ''f'' = x} \<union> {[x] |x. CHR ''g'' = x}  \<union> 
           {[x] |x. CHR ''h'' = x} \<union> {[x] |x. CHR ''i'' = x}  \<union> {[x] |x. CHR ''j'' = x} \<union> {[x] |x. CHR ''k'' = x} \<union> {[x] |x. CHR ''l'' = x}  \<union> {[x] |x. CHR ''m'' = x} \<union> {[x] |x. CHR ''n'' = x}  \<union> 
           {[x] |x. CHR ''o'' = x} \<union> {[x] |x. CHR ''p'' = x}  \<union> {[x] |x. CHR ''q'' = x} \<union> {[x] |x. CHR ''r'' = x} \<union> {[x] |x. CHR ''s'' = x}  \<union> {[x] |x. CHR ''t'' = x} \<union> {[x] |x. CHR ''u'' = x}  \<union> 
           {[x] |x. CHR ''v'' = x} \<union> {[x] |x. CHR ''w'' = x}  \<union> {[x] |x. CHR ''x'' = x} \<union> {[x] |x. CHR ''y'' = x} \<union> {[x] |x. CHR ''z'' = x} \<in> range lang"
    using 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 lang.simps(4)
    apply (simp  add: image_iff plus_set_def rangeI)  
    by (metis Symbolic_Regular_Algebra_Model.lang.simps(4) insert_is_Un plus_set_def)
  then show " {[x] |x.
     CHR ''a'' = x \<or>
     CHR ''b'' = x \<or>
     CHR ''c'' = x \<or>
     CHR ''d'' = x \<or>
     CHR ''e'' = x \<or>
     CHR ''f'' = x \<or>
     CHR ''g'' = x \<or>
     CHR ''h'' = x \<or>
     CHR ''i'' = x \<or>
     CHR ''j'' = x \<or>
     CHR ''k'' = x \<or>
     CHR ''l'' = x \<or>
     CHR ''m'' = x \<or>
     CHR ''n'' = x \<or>
     CHR ''o'' = x \<or> CHR ''p'' = x \<or> CHR ''q'' = x \<or> CHR ''r'' = x \<or> CHR ''s'' = x \<or> CHR ''t'' = x \<or> CHR ''u'' = x \<or> CHR ''v'' = x \<or> CHR ''w'' = x \<or> CHR ''x'' = x \<or> CHR ''y'' = x \<or> CHR ''z'' = x}
    \<in> range Symbolic_Regular_Algebra_Model.lang"
    using c1 apply auto done
qed


lemma alp_lem_uc:"{[x] |x. denote_ba uc x} \<in> range Symbolic_Regular_Algebra_Model.lang"
  apply(simp add:uc_def)
proof -
  have c1:"{[x] |x. CHR ''A'' = x}  \<union> {[x] |x. CHR ''B'' = x} \<union> {[x] |x. CHR ''C'' = x} \<union> {[x] |x. CHR ''D'' = x} \<union> {[x] |x. CHR ''E'' = x}  \<union> {[x] |x. CHR ''F'' = x} \<union> {[x] |x. CHR ''G'' = x}  \<union> 
           {[x] |x. CHR ''H'' = x} \<union> {[x] |x. CHR ''I'' = x}  \<union> {[x] |x. CHR ''J'' = x} \<union> {[x] |x. CHR ''K'' = x} \<union> {[x] |x. CHR ''L'' = x}  \<union> {[x] |x. CHR ''M'' = x} \<union> {[x] |x. CHR ''N'' = x}  \<union> 
           {[x] |x. CHR ''O'' = x} \<union> {[x] |x. CHR ''P'' = x}  \<union> {[x] |x. CHR ''Q'' = x} \<union> {[x] |x. CHR ''R'' = x} \<union> {[x] |x. CHR ''S'' = x}  \<union> {[x] |x. CHR ''T'' = x} \<union> {[x] |x. CHR ''U'' = x}  \<union> 
           {[x] |x. CHR ''V'' = x} \<union> {[x] |x. CHR ''W'' = x}  \<union> {[x] |x. CHR ''X'' = x} \<union> {[x] |x. CHR ''Y'' = x} \<union> {[x] |x. CHR ''Z'' = x} 
      =  {[x] |x.
     CHR ''A'' = x \<or>
     CHR ''B'' = x \<or>
     CHR ''C'' = x \<or>
     CHR ''D'' = x \<or>
     CHR ''E'' = x \<or>
     CHR ''F'' = x \<or>
     CHR ''G'' = x \<or>
     CHR ''H'' = x \<or>
     CHR ''I'' = x \<or>
     CHR ''J'' = x \<or>
     CHR ''K'' = x \<or>
     CHR ''L'' = x \<or>
     CHR ''M'' = x \<or>
     CHR ''N'' = x \<or>
     CHR ''O'' = x \<or> CHR ''P'' = x \<or> CHR ''Q'' = x \<or> CHR ''R'' = x \<or> CHR ''S'' = x \<or> CHR ''T'' = x \<or> CHR ''U'' = x \<or> CHR ''V'' = x \<or> CHR ''W'' = x \<or> CHR ''X'' = x \<or> CHR ''Y'' = x \<or> CHR ''Z'' = x}"
    by fastforce 
  have 2:"{[x] |x. CHR ''A'' = x} : range lang"
    using t1 by fastforce
  moreover have 3: "{[x] |x. CHR ''B'' = x} : range lang"
    using t1 by fastforce
  moreover have 4:"{[x] |x. CHR ''C'' = x} : range lang"
    using t1 by fastforce
  moreover have 5:"{[x] |x. CHR ''D'' = x} : range lang"
    using t1 by fastforce
  moreover have 6:"{[x] |x. CHR ''E'' = x} : range lang"
    using t1 by fastforce
  moreover have 7:"{[x] |x. CHR ''F'' = x} : range lang"
    using t1 by fastforce
  moreover have 8:"{[x] |x. CHR ''G'' = x} : range lang"
    using t1 by fastforce  
  moreover have 9:"{[x] |x. CHR ''H'' = x} : range lang"
    using t1 by fastforce
  moreover have 10:"{[x] |x. CHR ''I'' = x} : range lang"
    using t1 by fastforce
  moreover have 11:"{[x] |x. CHR ''J'' = x} : range lang"
    using t1 by fastforce
  moreover have 12:"{[x] |x. CHR ''K'' = x} : range lang"
    using t1 by fastforce
  moreover have 13:"{[x] |x. CHR ''L'' = x} : range lang"
    using t1 by fastforce
  moreover have 14:"{[x] |x. CHR ''M'' = x} : range lang"
    using t1 by fastforce
  moreover have 15:"{[x] |x. CHR ''N'' = x} : range lang"
    using t1 by fastforce
  moreover have 16:"{[x] |x. CHR ''O'' = x} : range lang"
    using t1 by fastforce
  moreover have 17:"{[x] |x. CHR ''P'' = x} : range lang"
    using t1 by fastforce
  moreover have 18:"{[x] |x. CHR ''Q'' = x} : range lang"
    using t1 by fastforce
  moreover have 19:"{[x] |x. CHR ''R'' = x} : range lang"
    using t1 by fastforce
  moreover have 20:"{[x] |x. CHR ''S'' = x} : range lang"
    using t1 by fastforce
  moreover have 21:"{[x] |x. CHR ''T'' = x} : range lang"
    using t1 by fastforce
  moreover have 22:"{[x] |x. CHR ''U'' = x} : range lang"
    using t1 by fastforce
  moreover have 23:"{[x] |x. CHR ''V'' = x} : range lang"
    using t1 by fastforce
  moreover have 24:"{[x] |x. CHR ''W'' = x} : range lang"
    using t1 by fastforce
  moreover have 25:"{[x] |x. CHR ''X'' = x} : range lang"
    using t1 by fastforce
  moreover have 26:"{[x] |x. CHR ''Y'' = x} : range lang"
    using t1 by fastforce
  moreover have 27:"{[x] |x. CHR ''Z'' = x} : range lang"
    using t1 by fastforce
  have "{[x] |x. CHR ''A'' = x}  \<union> {[x] |x. CHR ''B'' = x} \<union> {[x] |x. CHR ''C'' = x} \<union> {[x] |x. CHR ''D'' = x} \<union> {[x] |x. CHR ''E'' = x}  \<union> {[x] |x. CHR ''F'' = x} \<union> {[x] |x. CHR ''G'' = x}  \<union> 
           {[x] |x. CHR ''H'' = x} \<union> {[x] |x. CHR ''I'' = x}  \<union> {[x] |x. CHR ''J'' = x} \<union> {[x] |x. CHR ''K'' = x} \<union> {[x] |x. CHR ''L'' = x}  \<union> {[x] |x. CHR ''M'' = x} \<union> {[x] |x. CHR ''N'' = x}  \<union> 
           {[x] |x. CHR ''O'' = x} \<union> {[x] |x. CHR ''P'' = x}  \<union> {[x] |x. CHR ''Q'' = x} \<union> {[x] |x. CHR ''R'' = x} \<union> {[x] |x. CHR ''S'' = x}  \<union> {[x] |x. CHR ''T'' = x} \<union> {[x] |x. CHR ''U'' = x}  \<union> 
           {[x] |x. CHR ''V'' = x} \<union> {[x] |x. CHR ''W'' = x}  \<union> {[x] |x. CHR ''X'' = x} \<union> {[x] |x. CHR ''Y'' = x} \<union> {[x] |x. CHR ''Z'' = x} \<in> range lang"
    using 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 lang.simps(4)
    apply (simp  add: image_iff plus_set_def rangeI)  
    by (metis Symbolic_Regular_Algebra_Model.lang.simps(4) insert_is_Un plus_set_def)
  then show "  {[x] |x.
     CHR ''A'' = x \<or>
     CHR ''B'' = x \<or>
     CHR ''C'' = x \<or>
     CHR ''D'' = x \<or>
     CHR ''E'' = x \<or>
     CHR ''F'' = x \<or>
     CHR ''G'' = x \<or>
     CHR ''H'' = x \<or>
     CHR ''I'' = x \<or>
     CHR ''J'' = x \<or>
     CHR ''K'' = x \<or>
     CHR ''L'' = x \<or>
     CHR ''M'' = x \<or>
     CHR ''N'' = x \<or>
     CHR ''O'' = x \<or> CHR ''P'' = x \<or> CHR ''Q'' = x \<or> CHR ''R'' = x \<or> CHR ''S'' = x \<or> CHR ''T'' = x \<or> CHR ''U'' = x \<or> CHR ''V'' = x \<or> CHR ''W'' = x \<or> CHR ''X'' = x \<or> CHR ''Y'' = x \<or> CHR ''Z'' = x}
    \<in> range Symbolic_Regular_Algebra_Model.lang"
    using c1 apply auto done
qed
instantiation reg_lan ::  Ar_algebra
begin

  lift_definition alp_reg_lan :: "reg_lan set"
  is alpset
    apply(simp add:alpset_def)
    apply transfer  
    apply(erule disjE)
     apply (simp add: alp_lem_digit)
    apply(erule disjE)
     apply (simp add: alp_lem_lc)
    apply(simp add:alp_lem_uc)
    done

instance proof
  fix x :: "reg_lan"
  show "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
    by (metis kleene_algebra_class.dual.star2)
next                                         
  fix x :: "reg_lan"
  show "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
    by (rule kleene_algebra_class.star_unfoldr_eq)
next
  fix x :: "reg_lan"
  show "1 \<^bsup>& x\<^sup>\<star> = 1"
    apply(simp add:one_reg_lan_def inter_reg_lan_def star_reg_lan_def)
    by (smt (verit, best) Collect_cong one_reg_lan.rep_eq reg_lan.Abs_reg_lan_inverse Rep_reg_lan star_reg_lan.rep_eq insert_subset inter_set_def left_near_kleene_algebra_class.star_ref one_set_def singleton_conv2 singleton_iff)
next 
  fix x y z :: "reg_lan"
  show "1 \<^bsup>& y = 0 \<Longrightarrow> x = x \<cdot> y + z \<Longrightarrow> x = z \<cdot> y\<^sup>\<star>"
    by (metis one_reg_lan.rep_eq plus_reg_lan.rep_eq Rep_reg_lan_inject star_reg_lan.rep_eq times_reg_lan.rep_eq zero_reg_lan.rep_eq arden_r inter_empty inter_reg_lan.rep_eq)  
next
  fix x ::"reg_lan"
  show "0 \<^bsup>& x = 0"
    by simp
next
  fix x :: "reg_lan"
  show "(1 \<^bsup>& x \<noteq> 0) = (\<exists>y. x = 1 + y \<and> 1 \<^bsup>& y = 0)"
  proof -
    obtain t where "r_lang t = x"
      by (transfer, auto)
    moreover obtain t' where "t \<sim> ro(t) +\<^sub>r t'" "ro(t') = 0\<^sub>r"
      by (metis regexp_ewp)
    ultimately show ?thesis
      apply (transfer, auto)
      using zero_set_def apply auto[1]
      apply (simp add: zero_set_def)
      subgoal 
        apply (simp add:inter_set_def one_set_def one_list_def plus_set_def)
        by (smt (verit, del_insts) Symbolic_Regular_Algebra_Model.lang.simps(2) Symbolic_Regular_Algebra_Model.rexp.distinct(2) alpset_def bot.extremum emptyE insertE insert_is_Un insert_subsetI l_ewp_def neq_Nil_conv one_set_def rexp_ewp_l_ewp)
      subgoal 
      using zero_set_def by auto
    subgoal 
      by (metis inter_empty join.sup_left_idem l_ewp_def one_list_def one_set_def plus_ord_class.less_eq_def)
      done
  qed
next 
  fix x y :: "reg_lan"
  show "1 \<^bsup>& (x \<cdot> y) = 1 \<^bsup>& x \<^bsup>& y"
    apply (cases "1 \<^bsup>& x = 0")  
    subgoal 
      apply simp apply(cases "y =0")
      subgoal apply simp done
      subgoal apply(simp add:times_reg_lan_def one_reg_lan_def inter_reg_lan_def)
        by (smt (z3) Collect_cong one_reg_lan.rep_eq reg_lan.Rep_reg_lan_inverse times_reg_lan.rep_eq zero_reg_lan.rep_eq append_is_Nil_conv empty_Collect_eq inter_set_def l_prod_elim mem_Collect_eq one_list_def one_set_def singleton_conv2 zero_set_def)
      done
  apply (cases "1 \<^bsup>& y = 1")
  proof - 
    assume a1:"1 \<^bsup>& x \<noteq> 0"
    assume a2:"1 \<^bsup>& y = 1"
    show "1 \<^bsup>& (x \<cdot> y) = 1 \<^bsup>& x \<^bsup>& y"
    proof -
      from a1 have c1:"1 \<^bsup>& x = 1"
        by (smt (verit, del_insts) Collect_cong one_reg_lan.rep_eq reg_lan.Rep_reg_lan_inverse zero_reg_lan.abs_eq empty_Collect_eq inter_reg_lan.rep_eq inter_set_def one_set_def singletonD singleton_conv2 zero_set_def)
      from c1 a2 have c2:"1 \<^bsup>& (x \<cdot> y) = 1"
        apply (simp add: one_reg_lan_def inter_reg_lan_def times_reg_lan_def)
        by (metis Symbolic_Regular_Algebra_Model.one_reg_lan.rep_eq Symbolic_Regular_Algebra_Model.reg_lan.Abs_reg_lan_inverse Symbolic_Regular_Algebra_Model.reg_lan.Rep_reg_lan Symbolic_Regular_Algebra_Model.times_reg_lan.rep_eq inter_reg_lan.rep_eq lan_antimirow_l.A13)
      from c1 a2 have c3:"1 \<^bsup>& x \<^bsup>& y = 1"
        by auto 
      from c2 c3 show ?thesis 
        by auto 
    qed
  next 
    assume a1: "1 \<^bsup>& x \<noteq> 0"
    assume a2: "1 \<^bsup>& y \<noteq> 1"
    show "1 \<^bsup>& (x \<cdot> y) = 1 \<^bsup>& x \<^bsup>& y" 
    proof -
      from a1 have c1:"1 \<^bsup>& x = 1"
        by (smt (verit, del_insts) Collect_cong one_reg_lan.rep_eq reg_lan.Rep_reg_lan_inverse zero_reg_lan.abs_eq empty_Collect_eq inter_reg_lan.rep_eq inter_set_def one_set_def singletonD singleton_conv2 zero_set_def)
      then show ?thesis using a2
        by (smt (z3) Collect_cong one_reg_lan.rep_eq reg_lan.Rep_reg_lan_inject times_reg_lan.rep_eq append_is_Nil_conv inter_reg_lan.rep_eq inter_set_def l_prod_elim mem_Collect_eq one_list_def one_set_def singleton_conv2)
    qed
  qed
next 
  fix p :: "reg_lan"
  show "p \<in> \<bbbP> \<Longrightarrow> 1 \<^bsup>& p = 0"
    apply transfer
    apply (simp add: alpset_def) 
    apply (simp add: inter_set_def one_list_def one_set_def zero_set_def)
    by blast
next
  fix p q a b  :: "reg_lan"
  show "p \<in> \<bbbP> \<Longrightarrow> q \<in> \<bbbP> \<Longrightarrow> p \<cdot> a \<^bsup>& (q \<cdot> b) = p \<^bsup>& q \<cdot> (a \<^bsup>& b)"
    apply transfer
    apply(simp add:alpset_def c_prod_def inter_set_def times_list_def)  
    by (smt (verit) Collect_cong append_Cons append_self_conv2 list.inject mem_Collect_eq) 
next 
  fix p q a b  :: "reg_lan"
  show "p \<in> \<bbbP> \<Longrightarrow> q \<in> \<bbbP> \<Longrightarrow> a \<cdot> p \<^bsup>& (b \<cdot> q) = a \<^bsup>& b \<cdot> (p \<^bsup>& q)"
    apply transfer
    apply(simp add:alpset_def c_prod_def inter_set_def times_list_def)
    by fastforce
qed
end

instantiation reg_lan :: Al_algebra
begin

instance proof
  fix x :: "reg_lan"
  show "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis left_pre_kleene_algebra_class.star_unfoldl_eq)
next
  fix x y z :: "reg_lan"
  show " 1 \<^bsup>& y = 0 \<Longrightarrow> x = y \<cdot> x + z \<Longrightarrow> x = y\<^sup>\<star> \<cdot> z"
    by (metis one_reg_lan.rep_eq plus_reg_lan.rep_eq Rep_reg_lan_inject star_reg_lan.rep_eq times_reg_lan.rep_eq zero_reg_lan.rep_eq arden_l inter_empty inter_reg_lan.rep_eq)
qed
end

instance reg_lan :: A_algebra ..

theorem arden_regexp_l: 
  assumes "ro(y) = 0\<^sub>r" "x \<sim> y \<cdot>\<^sub>r x +\<^sub>r z" 
  shows "x \<sim> y\<^sup>\<star>\<^sub>r \<cdot>\<^sub>r z"
  using assms
  apply transfer
  by (metis Symbolic_Regular_Algebra_Model.lang.simps(4) Symbolic_Regular_Algebra_Model.lang.simps(5) Symbolic_Regular_Algebra_Model.lang.simps(6) Symbolic_Regular_Algebra_Model.rexp.distinct(2) arden_l rexp_ewp_l_ewp)

theorem arden_regexp_r: 
  assumes "ro(y) = 0\<^sub>r" "x \<sim> x \<cdot>\<^sub>r y +\<^sub>r z" 
  shows "x \<sim> z \<cdot>\<^sub>r y\<^sup>\<star>\<^sub>r"
  using assms
  apply transfer
  by (metis Symbolic_Regular_Algebra_Model.lang.simps(4) Symbolic_Regular_Algebra_Model.lang.simps(5) Symbolic_Regular_Algebra_Model.lang.simps(6) Symbolic_Regular_Algebra_Model.rexp.distinct(2) arden_r rexp_ewp_l_ewp)
 
end
