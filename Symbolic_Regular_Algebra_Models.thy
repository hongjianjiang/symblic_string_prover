theory Symbolic_Regular_Algebra_Models
  imports Symbolic_Regular_Algebra Regular_Algebra_Models
begin

section \<open>valid\<close>

definition valid :: "'a rexp \<Rightarrow> 'a rexp  \<Rightarrow>  bool"  where
"valid a b  = (lang a = lang b)"

section \<open>Consistent\<close>

primrec derive :: "('a rexp * 'a rexp) list \<Rightarrow> bool" where 
"derive [] =  True"|
"derive (p # ps) = (if valid (fst p) (snd p) then (derive ps) else False)"


definition consistent :: \<open>('a rexp * 'a rexp) set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> derive S'\<close>


instantiation reg_lan :: (type) antimirow_base begin



end
