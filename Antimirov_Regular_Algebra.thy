theory Antimirov_Regular_Algebra
  imports Main  Signatures 
begin

datatype ('a) Alpha = A | B | C

datatype 'a rexp= 
        Zero 
      | One 
      | Pred 'a
      | Plus "'a rexp" "'a rexp"
      | Times "'a rexp" "'a rexp"
      | Star "'a rexp"
      | Inter "'a rexp" "'a rexp"

type_synonym  'a Matrix = "'a list list"

class salomaa = zero + star_op + plus + times +
  fixes ewp :: "'a \<Rightarrow> bool"
  assumes S11: "x\<^sup>\<star> = (0\<^sup>\<star> + x)\<^sup>\<star>" and 
    EWP : "ewp x \<longleftrightarrow> (\<exists>y. x = 0\<^sup>\<star> + y \<and> \<not> ewp y)" and 
    S1 : "x + (y + z) = (x + y) + z" and 
    S2 : "x * (y * z) = (x * y) * z " and 
    S3 : "x + y = y + x" and 
    S4 : "x * (y + z) = x * y + x * z" and 
    S5 : "(x + y) * z = x * z + y * z" and 
    S6 : "x + x = x" and
    S7 : "0\<^sup>\<star> * a = a" and 
    S8 : "0 * a = 0" and 
    S9 : "x + 0 = x" and 
    S10 : "x\<^sup>\<star> = 0\<^sup>\<star> + x\<^sup>\<star> * x" and 
    SL : "\<lbrakk> \<not> ewp y; x = x * y + z \<rbrakk> \<Longrightarrow> x = z * y\<^sup>\<star>"
begin

definition tt1 :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
"tt1 a rs = map (\<lambda>i. (map (\<lambda>j. a * j) i)) rs"


definition sum_equations1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a " where 
"sum_equations1 a_values r_values r_matrix i n = 
          ((List.fold (+) (map (\<lambda>j. (*) (a_values ! j) (r_matrix !i ! j)) [0..<n+1]) 0) + (r_values ! i))"

fun reduce_plus :: "'a list \<Rightarrow> 'a" where
  "reduce_plus [] = 0"|
  "reduce_plus (x#xs) = x + reduce_plus xs"

definition component ::"'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
"component rmat as i n = List.fold (+) (map (\<lambda>j. (*) (as!i) (rmat!i!j)) [0..<n+1]) 0"


lemma aux_comp: "component rmat x i n = x!i*(rmat!i!n) + component rmat x i (n-1)"
  apply(auto simp:component_def)
  apply(induct n)
  apply simp 
  apply (simp add: local.S6 local.S9)
  apply simp
  done

definition ai_equals_rij :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where 
"ai_equals_rij als rls r_matrix i n = 
          (als!i = component r_matrix als i n + (rls!i))"

definition ewp_list where "ewp_list l = (filter (\<lambda>r. ewp r) l = [])"

definition ewp_matrix where "ewp_matrix ls = (ewp_list (concat ls) \<and> ([] \<notin> set ls) \<and> ls \<noteq> [])"

lemma ewp1: "ewp_list l \<Longrightarrow> \<forall>s \<in> set l. \<not> ewp s"
  apply(simp add:ewp_list_def)
  by (simp add: filter_empty_conv)

lemma ewp2: "ewp_matrix ls \<Longrightarrow> \<forall>s \<in> set (concat ls). \<not> ewp s"
  apply(simp add:ewp_matrix_def ewp_list_def)
  by (simp add: filter_empty_conv)

lemma "0 * 0 = 0"
  by (simp add: local.S8)

lemma "a * 0 * 0 = a * 0"
  by (metis local.S2 local.S8)

lemma t1: "a * 0 = (a * 0) * 0 + 0"
  by (metis local.S2 local.S8 local.S9)

lemma t2:"a * 0 = 0 * 0\<^sup>\<star>"
  using t1 SL 
  by (metis local.EWP local.S2 local.S8)

lemma "a * 0 = 0"
  using t2 S8 
  by simp

lemma t3: "a = a * 0 + a"
  by (simp add: local.S3 local.S8 local.S9 t2)

lemma "a * 0\<^sup>\<star> = a"
  by (metis local.EWP local.S1 local.S6 local.S8 local.SL t2 t3)

lemma base_r:"x = x * r11 + r1 \<Longrightarrow> y = y * r11 + r1 \<Longrightarrow> \<not> ewp r11 \<Longrightarrow> x = y"
  by (metis local.SL)

value "[[1::nat]]!0!0"

lemma base: "ai_equals_rij as rs rx 0 0 \<Longrightarrow> ewp_matrix rx \<Longrightarrow> as ! 0 = (rs ! 0) * (rx ! 0 !0)\<^sup>\<star>"
  apply (auto simp:ai_equals_rij_def ewp_matrix_def ewp_list_def component_def)
proof -
  assume a1:"as ! 0 = as ! 0 \<cdot> rx ! 0 ! 0 + 0 + rs ! 0" and a2: "filter ewp (concat rx) = []" and a3: "[] \<notin> set rx" and a4:" rx \<noteq> []  "
  then have "as ! 0 = as ! 0 \<cdot> rx ! 0 ! 0 + rs ! 0"
    by (simp add: local.S9)
  from a3 and a4 have "rx!0!0 \<in> set (concat rx)"
    apply auto
    by (metis hd_conv_nth hd_in_set)
  then have "\<not> ewp (rx ! 0 !0)" using a2 a3 ewp2  apply auto 
    by (metis \<open>rx ! 0 ! 0 \<in> set (concat rx)\<close> filter_empty_conv)
  then have "as ! 0 = (rs ! 0) * (rx ! 0 ! 0)\<^sup>\<star>"
    using \<open>as ! 0 = as ! 0 \<cdot> rx ! 0 ! 0 + rs ! 0\<close> local.SL by blast
  then show ?thesis apply auto done
qed


lemma "ai_equals_rij as rs rx n n \<Longrightarrow> as!n = component rx as n (n-1) + as!n * (rx!n!n) + rs!n"
  apply(simp add:ai_equals_rij_def) 
  by (metis One_nat_def aux_comp local.S3)


lemma "ai_equals_rij as rs rx 0 n \<Longrightarrow> ewp_matrix rx \<Longrightarrow> as ! 0 = (rs ! 0) * (rx ! 0 !0)\<^sup>\<star>"
  apply(auto simp:ewp_matrix_def ewp_list_def)
  apply(induct n)
  subgoal
    using base ewp_list_def ewp_matrix_def by presburger
  sorry

end

class REG = one + zero + times + plus + star_op + 
  fixes
    Reg :: "'a set"  and
    Alph :: "'a set"  and 
    inter :: "'a \<Rightarrow> 'a \<Rightarrow> 'a " (infixr "\<^bold>\<and>" 80)  
  assumes
    A1: "(a + b) + c = a + (b + c)" and
    A2: "(a * b) * c = a * (b * c)" and
    A3: "a + b = b + a" and
    A4: "a * (b + c) = a * b + a * c" and
    A5: "(a + b) * c = a * c + b * c" and
    A6: "a + a = a" and 
    A7: "a * 1 = a" and
    A8: "a * 0 = 0" and
    A9: "a + 0 = a" and
    A10: "1 + a * a\<^sup>\<star> =  a\<^sup>\<star>" and
    A11: "(1 + a)\<^sup>\<star> = a\<^sup>\<star>" and
    A12: "(1 \<^bold>\<and> b = 0) \<and> (a = b * a + c) \<Longrightarrow> a =  b\<^sup>\<star> * c" and
    A13: " 1 \<^bold>\<and> (a * b) = 1 \<^bold>\<and> a \<^bold>\<and> b" and
    A14: "1 \<^bold>\<and>  a\<^sup>\<star> = 1" and
    A15: "x \<in> Alph \<Longrightarrow> 1 \<^bold>\<and> x = 1" and
    A16: "0 \<^bold>\<and> a = 0" and
    A17: "a \<^bold>\<and> a = a" and
    A18: "a \<^bold>\<and> b = b \<^bold>\<and> a" and
    A19: "a \<^bold>\<and> (b \<^bold>\<and> c) = (a \<^bold>\<and> b) \<^bold>\<and> c" and
    A20: "a \<^bold>\<and> (b + c) = (a \<^bold>\<and> b) + (a \<^bold>\<and> c)" and
    A21: "a + (a \<^bold>\<and> b) = a" and
    A22: "x \<in> Alph \<and> y \<in> Alph \<Longrightarrow> (x * a) \<^bold>\<and> (y *  b) = (x * y) \<^bold>\<and> (a *  b)" and 
    A23: "x \<in> Alph \<and> y \<in> Alph \<Longrightarrow> (a * x) \<^bold>\<and> (b *  y) = (a * b) \<^bold>\<and> (x *  y)" and  
    A24: "x \<in> Alph \<and> y \<in> Alph \<Longrightarrow> x \<^bold>\<and> y = 0"

sublocale REG \<subseteq>  salomaa "(+)" "(\<cdot>)" 0 star ewp apply unfold_locales done

primrec rev :: "'a rexp \<Rightarrow> 'a rexp" where
  "rev Zero = Zero"|
  "rev One = One"|
  "rev (Pred x) = (Pred x)"|
  "rev (Plus a b) = Plus (rev a) (rev b)"|
  "rev (Times a b) = Times (rev b) (rev a)"|
  "rev (Inter a b) = Inter (rev b) (rev a)"|
  "rev (Star a) = Star (rev a)"
end

