theory Antimiro_Reguar_Algebra
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
          ((List.foldr (+) (map (\<lambda>j. (*) (a_values ! j) (r_matrix !i ! j)) [0..<n+1]) 0) + (r_values ! i))"

value "[0..<1] ! 0"

lemma "sum_equations1 [a] [r1,r2] [[c],[d]] 0 0 = (a * c) + 0 + r1"
  apply(simp add:sum_equations1_def) 
  done

definition sum_equations :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where 
"sum_equations a_values r_values r_matrix i n = 
          (a_values !i = (List.foldr (+) (map (\<lambda>j. (*) (a_values ! j) (r_matrix !i ! j)) [0..<n]) 0) + (r_values ! i))"

definition ewp_list where "ewp_list l = (filter (\<lambda>r. ewp r) l = [])"

definition ewp_matrix where "ewp_matrix l = (filter (\<lambda>r. ewp_list r) l = [])"

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


lemma "sum_equations as rs rx 0 0 \<Longrightarrow> ewp_matrix rx \<Longrightarrow> as ! 0 = (rs ! 0) * (rx ! 0 !0)\<^sup>\<star>"
  apply (simp add:sum_equations_def ewp_matrix_def ewp_list_def)
  nitpick
    
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

