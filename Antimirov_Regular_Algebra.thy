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

fun reduce_plus :: "'a list \<Rightarrow> 'a" where
  "reduce_plus [] = 0"|
  "reduce_plus (x#xs) = x + reduce_plus xs"

definition sum_rexp ::"'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where (* \<Sum>(j=0-n). ai * rij + 0 *)
"sum_rexp r a i n = List.fold (+) (map (\<lambda>j. (*) (a!i) (r!i!j)) [0..<n+1]) 0"

  
lemma aux_comp: "sum_rexp rmat x i n = x!i*(rmat!i!n) + sum_rexp rmat x i (n-1)"
  apply(auto simp:sum_rexp_def)
  apply(induct n)
  apply simp 
  apply (simp add: local.S6 local.S9)
  apply simp
  done

definition matrix_ewp :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> bool" where
"matrix_ewp a l r n = (length a = (n+1) \<and> length r = (n+1)  \<and> (\<forall>l\<in>set r. length l = (n+1)) \<and> length l = (n+1))"


definition ai_equals_rij :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> bool" where 
"ai_equals_rij a l r n = 
          (\<forall>i\<in> set [0..<n+1]. a!i = sum_rexp r a i n + (l!i))"

definition ai_equals_rij' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> bool" where 
"ai_equals_rij' als rls r_matrix n = 
    (\<forall>i\<in> set [0..<n]. als!i = List.fold (+) 
(map (\<lambda>j. (*) (als!i) ((r_matrix!i!j) + r_matrix!n!j * (r_matrix!n!n)\<^sup>\<star> * (r_matrix!i!n))) [0..<n+1]) 0 + (rls!i + rls!n*(r_matrix!n!n)\<^sup>\<star> * (r_matrix!i!n)))"

definition ewp_list where "ewp_list l = (filter (\<lambda>r. ewp r) l = [])"

definition ewp_matrix where "ewp_matrix ls = (ewp_list (concat ls) \<and> [] \<notin> set ls \<and> ls \<noteq> [])"

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

lemma base: "ai_equals_rij as rs rx 0 \<Longrightarrow> ewp_matrix rx \<Longrightarrow> as ! 0 = (rs ! 0) * (rx ! 0 !0)\<^sup>\<star>"
  apply (auto simp:ai_equals_rij_def ewp_matrix_def ewp_list_def sum_rexp_def)
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

 (* an = \<Sum>j=1-(n-1)aj * rnj + an* rnn + rn \<Rightarrow> an = (\<Sum>j=1-(n-1)aj * rnj + rn) * rnn\<^sup>* *)
lemma "matrix_ewp a l r n \<Longrightarrow> ewp_matrix r \<Longrightarrow> a!n = sum_rexp r a n (n-1) + a!n * r!n!n + l!n \<Longrightarrow> a!n = (sum_rexp r a n (n-1) + l!n) * (r!n!n)\<^sup>\<star>"
  apply (simp add:ewp_matrix_def ewp_list_def sum_rexp_def matrix_ewp_def)
  apply auto
  by (smt (verit) UN_I filter_empty_conv lessI local.S1 local.S3 local.SL nth_mem set_concat)

lemma "ai_equals_rij as rs rx n \<Longrightarrow> as!n = sum_rexp rx as n (n-1) + as!n * (rx!n!n) + rs!n"
  apply(simp add:ai_equals_rij_def) 
  by (metis One_nat_def aux_comp local.S3)

lemma aux1:"\<not> ewp (rx!n!n) \<Longrightarrow> as!n = sum_rexp rx as n (n-1) + as!n * (rx!n!n) + rs!n ==> as!n = (sum_rexp rx as n (n-1) + rs!n) * (rx!n!n)\<^sup>\<star>"
proof -
  assume "as ! n = sum_rexp rx as n (n - 1) + as ! n \<cdot> rx ! n ! n + rs ! n" and a1: "\<not> ewp (rx!n!n)"
  then have "as ! n = as ! n \<cdot> rx ! n ! n + (sum_rexp rx as n (n - 1) + rs ! n)"
    by (metis local.S1 local.S3)
  then show ?thesis  using a1 
    using local.SL by blast
qed


lemma aux2: "matrix_ewp a l r n \<Longrightarrow>  ai_equals_rij a l r  n \<Longrightarrow> ewp_matrix r \<Longrightarrow>  a!n = (sum_rexp r a n (n-1) + l!n) * (r!n!n)\<^sup>\<star>"
  apply(auto simp:ewp_matrix_def ewp_list_def ai_equals_rij_def matrix_ewp_def)
  apply(induct n)  
  apply (smt (verit) UN_I aux1 aux_comp ewp2 ewp_list_def ewp_matrix_def length_greater_0_conv local.S3 nth_mem set_concat zero_diff)
  by (metis One_nat_def UN_I aux1 aux_comp filter_empty_conv lessI local.S3 nth_mem set_concat)


lemma ec_0: "ewp_list xs \<Longrightarrow> 0 = List.fold (+) (map (\<lambda>x. 0 * x) xs) 0 + 0"
  apply(induct xs)
  apply simp 
  apply (simp add: local.S9)
  by (metis ewp_list_def filter_empty_conv fold_simps(2) list.set_intros(2) list.simps(9) local.S8 t3) 

lemma ec_x_aux1:"0 = fold (+) (map (\<lambda>i. 0 \<cdot> i) (xs)) 0"
  apply (induct xs)
  apply simp
  apply simp 
  by (metis local.S8 local.S9)

lemma ec_x: "ewp_list xs \<Longrightarrow>  0< i \<and> i\<le>length xs\<Longrightarrow> xs ! i = List.fold (+) (map (\<lambda>i. 0 * i) ((take (i-1) xs) @ drop (length xs -i) xs)) 0 + 0 + 0\<^sup>\<star> * xs!i"
proof -
  assume a1:"ewp_list xs" and a2:"0 < i \<and> i \<le> length xs"
  then have "0 = fold (+) (map ((\<cdot>) 0) (take (i - 1) xs @ drop (length xs - i) xs)) 0"
    using ec_x_aux1 by blast
  moreover have "xs ! i = 0 + 0 + 0\<^sup>\<star> \<cdot> xs ! i "
    using local.S7 local.S8 t2 t3 by auto
  then show "xs ! i = fold (+) (map ((\<cdot>) 0) (take (i - 1) xs @ drop (length xs - i) xs)) 0 + 0 + 0\<^sup>\<star> \<cdot> xs ! i"
    using ec_x_aux1 by presburger
qed

lemma ec_one: "0\<^sup>\<star> = List.fold (+) (map (\<lambda>x. 0 * x) xs) 0 + 0\<^sup>\<star>  "
  using ec_x_aux1 local.S8 t2 t3 by auto


lemma equivlance: "ai_equals_rij as rs rx n \<Longrightarrow> ai_equals_rij bs rs rx n \<Longrightarrow> \<forall>i\<in>set[0..<n+1]. as!i = b!i"
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

