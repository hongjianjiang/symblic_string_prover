theory Ostrich_Sequent 
  imports Symbolic_Regular_Algebra_Model "HOL-Library.Countable"
begin

section \<open>Miscellaneous Utilities\<close>

text \<open>Some facts about (in)finite sets\<close>

theorem set_inter_compl_diff [simp]: \<open>- A \<inter> B = B - A\<close> by blast

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:tms} The datatypes of tms and formulae are defined as follows:
\<close>
type_synonym id = String.literal

datatype tm = Var id | Fn id "tm list" | Reg (regcl: "char BA rexp")

datatype 'a fm = Truth | Falsity | Atom 'a | Imp "'a fm" "'a fm" | Iff "'a fm" "'a fm" |
    And "'a fm" "'a fm" | Or "'a fm" "'a fm" | Not "'a fm"

datatype fol = Rl id "tm list"

term "Atom (Rl (STR '':'') [Var STR ''x'', Reg One])"
term "Atom (Rl (STR ''='') [Var STR ''z'', Fn i [Var STR ''x'', Var STR ''y'']])"

datatype "thm" = Thm (concl: "fol fm")

subsection \<open>Definition of rules and axioms\<close>

abbreviation (input) "fail_thm \<equiv> Thm Truth"

definition fol_equal :: "fol fm \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "fol_equal p q \<equiv> p = q"

definition zip_eq :: "tm list \<Rightarrow> tm list \<Rightarrow> fol fm list"
where
  "zip_eq l l' \<equiv> map (\<lambda>(t, t'). Atom (Rl (STR ''='') [t, t'])) (zip l l')"

primrec occurs_in :: "id \<Rightarrow> tm \<Rightarrow> bool" and occurs_in_list :: "id \<Rightarrow> tm list \<Rightarrow> bool"
where
  "occurs_in i (Var x) = (i = x)" |
  "occurs_in i (Fn _ l) = occurs_in_list i l" |
  "occurs_in_list _ [] = False" |
  "occurs_in_list i (h # t) = (occurs_in i h \<or> occurs_in_list i t)"

primrec free_in :: "id \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "free_in _ Truth = False" |
  "free_in _ Falsity = False" |
  "free_in i (Atom a) = (case a of Rl _ l \<Rightarrow> occurs_in_list i l)" |
  "free_in i (Imp p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Iff p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (And p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Or p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Not p) = free_in i p" 

primrec equal_length :: "tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "equal_length l [] = (case l of [] \<Rightarrow> True | _ # _ \<Rightarrow> False)" |
  "equal_length l (_ # r') = (case l of [] \<Rightarrow> False | _ # l' \<Rightarrow> equal_length l' r')"

subsection \<open>Semantics of first-order logic\<close>

definition length2 :: "tm list \<Rightarrow> bool"
where
  "length2 l \<equiv> case l of [_,_] \<Rightarrow> True | _ \<Rightarrow> False"

primrec \<comment> \<open>Semantics of terms\<close>
  semantics_term :: "(id \<Rightarrow> char list) \<Rightarrow> (id \<Rightarrow> char list set list \<Rightarrow> char list set) \<Rightarrow> tm \<Rightarrow> char list set" and
  semantics_list :: "(id \<Rightarrow> char list) \<Rightarrow> (id \<Rightarrow> char list set list \<Rightarrow> char list set) \<Rightarrow> tm list \<Rightarrow> char list set list"
where
  "semantics_term e _ (Var x) = {e x}" |
  "semantics_term e _ (Reg r) = lang r" |
  "semantics_term e f (Fn i l) = f i (semantics_list e f l)" |
  "semantics_list _ _ [] = []" |
  "semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec \<comment> \<open>Semantics of formulas\<close>
  semantics ::
    "(id \<Rightarrow> char list)  \<Rightarrow> (id \<Rightarrow> char list set list \<Rightarrow> char list set) \<Rightarrow> (id \<Rightarrow> char list set list \<Rightarrow> bool) \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "semantics _ _ _ Truth = True" |
  "semantics _ _ _ Falsity = False" |
  "semantics e f g (Atom a) = (case a of Rl i l \<Rightarrow> if i = STR ''='' \<and> length2 l
      then (semantics_term e f (hd l) = semantics_term e f (hd (tl l)))
      else if i = STR ''~='' \<and> length2 l  
      then (semantics_term e f (hd l) \<noteq> semantics_term e f (hd (tl l)))
      else if i = STR '':'' \<and> length2 l  
      then (semantics_term e f (hd l) \<subseteq> semantics_term e f (hd (tl l)))
      else if i = STR ''~:'' \<and> length2 l  
      then \<not> (semantics_term e f (hd l) \<subseteq> semantics_term e f (hd (tl l)))
      else g i (semantics_list e f l))" |
  "semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)" |
  "semantics e f g (Iff p q) = (semantics e f g p \<longleftrightarrow> semantics e f g q)" |
  "semantics e f g (And p q) = (semantics e f g p \<and> semantics e f g q)" |
  "semantics e f g (Or p q) = (semantics e f g p \<or> semantics e f g q)" |
  "semantics e f g (Not p) = (\<not> semantics e f g p)"


subsection \<open>Definition of proof system\<close>


definition not_memberI :: "thm  \<Rightarrow> thm" where
  "not_memberI s \<equiv> case concl s of Atom p \<Rightarrow> case p of Rl i l \<Rightarrow> if i = STR '':'' \<and> length2 l
      then  Thm (Atom (Rl STR ''~:'' l))
      else  fail_thm | _ \<Rightarrow> fail_thm"

inductive sequent :: "fol fm list \<Rightarrow> bool" ("\<stileturn> _" 0) where
  andI: "\<stileturn> [p, p'] @ \<Gamma> \<Longrightarrow> \<stileturn> [(And p p')] @ \<Gamma>" |
  neg_orI: "\<stileturn> [Not p, Not p'] @ \<Gamma> \<Longrightarrow> \<stileturn> [Not (Or p p')] @ \<Gamma>" |
  orI: "\<stileturn> [p] @ \<Gamma> \<Longrightarrow> \<stileturn> [p'] @ \<Gamma> \<Longrightarrow> \<stileturn> [Or p p'] @ \<Gamma>" |
  neg_andI: "\<stileturn> [Not p] @ \<Gamma> \<Longrightarrow> \<stileturn> [Not p'] @ \<Gamma> \<Longrightarrow> \<stileturn> [Not (And p p')] @ \<Gamma>" |
  neg_negI: "\<stileturn> [p] @ \<Gamma> \<Longrightarrow> \<stileturn> [Not (Not p)] @ \<Gamma>" |
  not_memberI: "regexp_compl e ec \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e])] @ \<Gamma> \<Longrightarrow>
                \<stileturn> [Atom (Rl STR ''~:'' [x, Reg ec])] @ \<Gamma>" |
  not_eq: "\<not> occurs_in_list y (x#xs) \<Longrightarrow> \<stileturn> [Atom (Rl STR ''~='' [x,Var y]), Atom (Rl STR ''='' [Var y, Fn i xs])] @ \<Gamma> \<Longrightarrow> 
           \<stileturn> [Atom (Rl STR ''~='' [x, Fn i xs])] @ \<Gamma>" |
  cut: "regexp_compl e ec \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e])] @ \<Gamma> \<Longrightarrow> \<stileturn> [Atom (RL STR '':'' [x, Reg ec])] @ \<Gamma> \<Longrightarrow> \<stileturn> \<Gamma>" |
  eq_prop: "\<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR ''='' [x, y]), Atom (Rl STR '':'' [x, Reg e])] @ \<Gamma>  \<Longrightarrow>
            \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR ''='' [x, y])] @ \<Gamma>" | 
  neq_subsume: "regexp_empty e1 e2 \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e1]), Atom (Rl STR '':'' [y, Reg e2])] @ \<Gamma> 
            \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e1]), Atom (Rl STR ''~='' [x, y]), Atom (Rl STR '':'' [y, Reg e2])] @ \<Gamma>" |
  eq_prop_elim : "is_singleton (lang e) \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR '':'' [y, Reg e])] @ \<Gamma> \<Longrightarrow>
                  \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR ''='' [x, y])]" |
  neq_prop_elim : "is_singleton (lang e) \<Longrightarrow> regexp_compl e ec \<Longrightarrow>  \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR '':'' [y, Reg ec])] @ \<Gamma> \<Longrightarrow>
                  \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR ''~='' [x, y])]" | 
  close: "empty_intersection_set es \<Longrightarrow> \<stileturn> map (\<lambda>e. (Atom (Rl STR '':'' [x, Reg e]))) es @ \<Gamma> " | 
  subsume: "subset_intersect_set e es \<Longrightarrow> \<stileturn> map (\<lambda>r. Atom (Rl STR '':'' [x, Reg r])) es @ \<Gamma> \<Longrightarrow> 
           \<stileturn> Atom (Rl STR '':'' [x, Reg e]) # (map (\<lambda>r. Atom (Rl STR '':'' [x, Reg r])) es) @ \<Gamma>" |
  intersect: "eq_len_intersect e es \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e])] @ \<Gamma> \<Longrightarrow> 
             \<stileturn> map (\<lambda>r. Atom (Rl STR '':'' [x, Reg r])) es @ \<Gamma>" |
  fwd_prop: "con_fwd_prop e e1 e2 \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR ''='' [x, Fn i [x1,x2]]), 
             Atom (Rl STR '':'' [x1, Reg e1]), Atom (Rl STR '':'' [x2, Reg e2])] @ \<Gamma> \<Longrightarrow>
             \<stileturn> [Atom (Rl STR ''='' [x, Fn i [x1,x2]]), 
             Atom (Rl STR '':'' [x1, Reg e1]), Atom (Rl STR '':'' [x2, Reg e2])] @ \<Gamma>" |
  fwd_prop_elim: "con_fwd_prop_elim e e1 e2 \<Longrightarrow> \<stileturn> [Atom (Rl STR '':'' [x, Reg e]), Atom (Rl STR '':'' [x1, Reg e1]), Atom (Rl STR '':'' [x1, Reg e2])] @ \<Gamma> \<Longrightarrow>
                 \<stileturn> [Atom (Rl STR ''='' [x, Fn i [x1,x2]]), Atom (Rl STR '':'' [x1, Reg e1]), Atom (Rl STR '':'' [x1, Reg e2])] @ \<Gamma>"
  
declare sequent.intros [intro]

section \<open>Soundness\<close>

value "e(x := v)"
lemma map':
  "\<not> occurs_in x t \<Longrightarrow> semantics_term e f t = semantics_term (e(x := v)) f t"
  "\<not> occurs_in_list x l \<Longrightarrow> semantics_list e f l = semantics_list (e(x := v)) f l"
by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma map:
  "\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p"
proof (induct p arbitrary: e)
  fix e
  show "\<not> free_in x Truth \<Longrightarrow> semantics e f g Truth \<longleftrightarrow> semantics (e(x := v)) f g Truth"
  by simp
next
  fix e
  show "\<not> free_in x Falsity \<Longrightarrow> semantics e f g Falsity \<longleftrightarrow> semantics (e(x := v)) f g Falsity"
  by simp
next
  fix a e
  show "\<not> free_in x (Atom a) \<Longrightarrow> semantics e f g (Atom a) \<longleftrightarrow> semantics (e(x := v)) f g (Atom a)"
  proof (cases a)
    fix i l
    show "\<not> free_in x (Atom a) \<Longrightarrow> a = Rl i l \<Longrightarrow>
        semantics e f g (Atom a) \<longleftrightarrow> semantics (e(x := v)) f g (Atom a)"
    proof -
      assume assm: "\<not> free_in x (Atom a)" "a = Rl i l"
      then have fresh: "\<not> occurs_in_list x l"
      by simp
      show "semantics e f g (Atom a) \<longleftrightarrow> semantics (e(x := v)) f g (Atom a)"
      proof cases
        assume eq: "i = STR ''='' \<and> length2 l"
        then have "semantics e f g (Atom (Rl i l)) \<longleftrightarrow>
            semantics_term e f (hd l) = semantics_term e f (hd (tl l))"
        by simp
        also have "... \<longleftrightarrow>
            semantics_term (e(x := v)) f (hd l) = semantics_term (e(x := v)) f (hd (tl l))"
        using map'(1) fresh occurs_in_list.simps(2) eq list.case_eq_if list.collapse
        unfolding length2_def
        by metis
        finally show ?thesis
        using eq assm(2)
        by simp
      next
        assume not_eq: "\<not> (i = STR ''='' \<and> length2 l)"
        then show ?thesis 
        proof cases  
          assume neq: "i = STR ''~='' \<and> length2 l"
        then have "semantics e f g (Atom (Rl i l))  \<longleftrightarrow>
            semantics_term e f (hd l) \<noteq> semantics_term e f (hd (tl l))"
        by simp
        also have "...  \<longleftrightarrow>
            semantics_term (e(x := v)) f (hd l) \<noteq> semantics_term (e(x := v)) f (hd (tl l))"
        using map'(2) fresh 
        by (metis length2_def list.case_eq_if list.split_sel_asm map'(1) neq occurs_in_list.simps(2))
        finally show ?thesis 
          by (simp add: assm(2) neq)
      next 
        assume neq1: "\<not> (i = STR ''='' \<and> length2 l)" and
               neg2: "\<not> (i = STR ''~='' \<and> length2 l) "
        then show ?thesis 
        proof cases 
          assume mem: "i = STR '':'' \<and> length2 l"
          then have "semantics e f g (Atom (Rl i l))  \<longleftrightarrow>
            semantics_term e f (hd l) \<subseteq> semantics_term e f (hd (tl l))"
            by simp
          also have "...  \<longleftrightarrow>
            semantics_term (e(x := v)) f (hd l) \<subseteq> semantics_term (e(x := v)) f (hd (tl l))"
            by (metis fresh length2_def list.case_eq_if list.collapse map'(1) mem occurs_in_list.simps(2))
          finally show ?thesis 
            by (simp add: assm(2) mem)
        next 
          assume 1: "\<not> (i = STR ''='' \<and> length2 l)" and 2:" \<not> (i = STR ''~='' \<and> length2 l)" and 3 :"\<not> (i = STR '':'' \<and> length2 l)"
          then show ?thesis 
          proof cases 
            assume nmem: "i = STR ''~:'' \<and> length2 l"
            then have "semantics e f g (Atom (Rl i l))  \<longleftrightarrow>
            \<not> (semantics_term e f (hd l) \<subseteq> semantics_term e f (hd (tl l)))"
            by simp
          also have "...  \<longleftrightarrow>
            \<not> (semantics_term (e(x := v)) f (hd l) \<subseteq> semantics_term (e(x := v)) f (hd (tl l)))"
            by (metis fresh length2_def list.case_eq_if list.collapse map'(1) nmem occurs_in_list.simps(2))
          finally show ?thesis 
            by (simp add: assm(2) nmem)
        next 
          assume not_eq: "\<not> (i = STR ''='' \<and> length2 l)" and 2:"\<not> (i = STR ''~='' \<and> length2 l)" and 3:"\<not> (i = STR '':'' \<and> length2 l)" and 4:"\<not> (i = STR ''~:'' \<and> length2 l)"

        then have "semantics e f g (Atom (Rl i l)) \<longleftrightarrow> g i (semantics_list e f l)"
        by simp iprover
        also have "... \<longleftrightarrow> g i (semantics_list (e(x := v)) f l)"
        using map'(2) fresh
        by metis
        finally show ?thesis 
          by (simp add: "3" "4" assm(2) local.not_eq neg2)
        qed
      qed
    qed
  qed
qed 
qed
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (Imp p1 p2) \<Longrightarrow>
      semantics e f g (Imp p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Imp p1 p2)"
  using assm1 assm2
  by simp
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (Iff p1 p2) \<Longrightarrow>
      semantics e f g (Iff p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Iff p1 p2)"
  using assm1 assm2
  by simp
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (And p1 p2) \<Longrightarrow>
      semantics e f g (And p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (And p1 p2)"
  using assm1 assm2
  by simp
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (Or p1 p2) \<Longrightarrow>
      semantics e f g (Or p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Or p1 p2)"
  using assm1 assm2
  by simp
next
  fix p e
  assume "\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p" for e
  then show "\<not> free_in x (Not p) \<Longrightarrow> semantics e f g (Not p) \<longleftrightarrow> semantics (e(x := v)) f g (Not p)"
  by simp
qed

lemma length2_equiv:
  "length2 l \<longleftrightarrow> [hd l, hd (tl l)] = l"
proof -
  have "length2 l \<Longrightarrow> [hd l, hd (tl l)] = l"
  unfolding length2_def
  using list.case_eq_if list.exhaust_sel
  by metis
  then show ?thesis
  unfolding length2_def
  using list.case list.case_eq_if
  by metis
qed

lemma equal_length_sym:
  "equal_length l l' \<Longrightarrow> equal_length l' l"
proof (induct l' arbitrary: l)
  fix l
  assume "equal_length l []"
  then show "equal_length [] l"
  using equal_length.simps list.case_eq_if
  by metis
next
  fix l l' a
  assume sym: "equal_length l l' \<Longrightarrow> equal_length l' l" for l
  assume "equal_length l (a # l')"
  then show "equal_length (a # l') l"
  using equal_length.simps list.case_eq_if list.collapse list.inject sym
  by metis
qed

lemma equal_length2:
  "equal_length l l' \<Longrightarrow> length2 l \<longleftrightarrow> length2 l'"
proof -
  assume assm: "equal_length l l'"
  have "equal_length l [t, t'] \<Longrightarrow> length2 l" for t t'
  unfolding length2_def
  using equal_length.simps list.case_eq_if
  by metis
  moreover have "equal_length [t, t'] l' \<Longrightarrow> length2 l'" for t t'
  unfolding length2_def
  using equal_length.simps list.case_eq_if equal_length_sym
  by metis
  ultimately show ?thesis
  using assm length2_equiv
  by metis
qed

lemma imp_chain_equiv:
  "semantics e f g (foldr Imp l p) \<longleftrightarrow> (\<forall>q \<in> set l. semantics e f g q) \<longrightarrow> semantics e f g p"
using imp_conjL
by (induct l) simp_all

lemma imp_chain_zip_eq:
  "equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') p) \<longleftrightarrow>
      semantics_list e f l = semantics_list e f l' \<longrightarrow> semantics e f g p"
proof -
  assume "equal_length l l'"
  then have "(\<forall>q \<in> set (zip_eq l l'). semantics e f g q) \<longleftrightarrow>
      semantics_list e f l = semantics_list e f l'"
  unfolding zip_eq_def
  using length2_def
  by (induct l l' rule: list_induct2') simp_all
  then show ?thesis
  using imp_chain_equiv
  by iprover
qed

lemma funcong:
  "equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') (Atom (Rl (STR ''='') [Fn i l, Fn i l'])))"
proof -
  assume assm: "equal_length l l'"
  show ?thesis
  proof cases
    assume "semantics_list e f l = semantics_list e f l'"
    then have "semantics e f g (Atom (Rl (STR ''='') [Fn i l, Fn i l']))"
    using length2_def
    by simp
    then show ?thesis
    using imp_chain_equiv
    by iprover
  next
    assume "semantics_list e f l \<noteq> semantics_list e f l'"
    then show ?thesis
    using assm imp_chain_zip_eq
    by iprover
  qed
qed

lemma predcong:
  "equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') (Imp (Atom (Rl i l)) (Atom (Rl i l'))))"
proof -
  assume assm: "equal_length l l'"
  show ?thesis
  proof cases
    assume eq: "i = STR ''='' \<and> length2 l \<and> length2 l'"
    show ?thesis
    proof cases
      assume "semantics_list e f l = semantics_list e f l'"
      then have "semantics_list e f [hd l, hd (tl l)] = semantics_list e f [hd l', hd (tl l')]"
      using eq length2_equiv
      by simp
      then have "semantics e f g (Imp (Atom (Rl (STR ''='') l)) (Atom (Rl (STR ''='') l')))"
      using eq
      by simp
      then show ?thesis
      using eq imp_chain_equiv
      by iprover
    next
      assume "semantics_list e f l \<noteq> semantics_list e f l'"
      then show ?thesis
      using assm imp_chain_zip_eq
      by iprover
    qed
  next
    assume not_eq: "\<not> (i = STR ''='' \<and> length2 l \<and> length2 l')"
    show ?thesis
    proof cases
      assume "semantics_list e f l = semantics_list e f l'"
      then have "semantics e f g (Imp (Atom (Rl i l)) (Atom (Rl i l')))"
      using assm not_eq equal_length2 
      by (smt (verit, ccfv_threshold) fol.case length2_equiv list.inject semantics.simps(3) semantics.simps(4) semantics_list.simps(2))
      then show ?thesis
      using imp_chain_equiv
      by iprover
    next
      assume "semantics_list e f l \<noteq> semantics_list e f l'"
      then show ?thesis
      using assm imp_chain_zip_eq
      by iprover
    qed
  qed
qed

lemma One_SC_soundness: \<open>\<stileturn> G \<Longrightarrow> (\<exists>p \<in> set G. \<not> semantics e f g p)\<close>
proof (induct G  arbitrary: e rule: sequent.induct)
  case (andI p p' \<Gamma>)
  then show ?case apply auto done
next
  case (neg_orI p p' \<Gamma>)
  then show ?case apply auto done
next
  case (orI p \<Gamma> p')
  then show ?case apply auto done
next
  case (neg_andI p \<Gamma> p')
  then show ?case apply auto done
next
  case (neg_negI p \<Gamma>)
  then show ?case apply auto done
next
  case (not_memberI e ec x \<Gamma>)
  then show ?case apply auto sorry
next
  case (not_eq y x xs i \<Gamma>)
  then show ?case apply simp sorry  
next
  case (cut e ec x \<Gamma> RL)
  then show ?case  apply auto sorry
next
  case (eq_prop x e y \<Gamma>)
  then show ?case sorry
next
  case (neq_subsume e1 e2 x y \<Gamma>)
  then show ?case sorry
next
  case (eq_prop_elim e x y \<Gamma>)
  then show ?case sorry
next
  case (neq_prop_elim e ec x y \<Gamma>)
  then show ?case sorry
next
  case (close es x \<Gamma>)
  then show ?case sorry
next
  case (subsume e es x \<Gamma>)
  then show ?case sorry
next
  case (intersect e es x \<Gamma>)
  then show ?case sorry
next
  case (fwd_prop e e1 e2 x i x1 x2 \<Gamma>)
  then show ?case sorry
next
  case (fwd_prop_elim e e1 e2 x x1 \<Gamma> i x2)
  then show ?case sorry
qed
 

(*next
  case (Bwd_PropConc e es x1 x2 x \<Gamma>)
  then show ?case apply (auto simp:c_prod_def times_list_def) sorry*)

definition one_sc_proof :: \<open>(char BA) form list \<Rightarrow> (char BA) form \<Rightarrow> bool\<close> where
  \<open>one_sc_proof ps p \<equiv> (\<stileturn>  Neg p # ps)\<close>

theorem sc_soundness:
  \<open>one_sc_proof ps p \<Longrightarrow> list_all \<lbrakk>E, (@)\<rbrakk> ps \<Longrightarrow> \<lbrakk>E, (@)\<rbrakk> p\<close>
  using One_SC_soundness unfolding one_sc_proof_def list_all_def
  by fastforce

section \<open>Completeness\<close>  


subsection \<open>Consistent sets\<close>

definition consistency :: "(char BA) form set set \<Rightarrow> bool" where
  "consistency C = (\<forall>S. S \<in> C \<longrightarrow> 
              (\<forall> A B. Con A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
              (\<forall> A B. Neg (Dis A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and> 
              (\<forall> A B. Dis A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and> 
              (\<forall> A B. Neg (Con A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and> 
              (\<forall> A. Neg (Neg A) \<in> S \<longrightarrow> S \<union> {A} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> Member neg x e \<in> S \<longrightarrow> S \<union> {Member pos x ec} \<in> C) \<and> 
              (\<forall> x y p q. EqAtom neg  x (Conc p q) \<in> S \<longrightarrow> S \<union> {EqFresh neg  x y, EqFresh pos y (Conc p q)} \<in> C) \<and> 
              (\<forall> x e ec. regexp_compl e ec \<longrightarrow> S \<union> {Member pos x e} \<in> C \<longrightarrow> S \<union> {Member pos x ec} \<in> C \<longrightarrow> S \<in> C) \<and> 
              (\<forall> x y e. Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x y, Member pos y e} \<in> C) \<and> 
              (\<forall> e1 e2 x y. regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> S \<and> EqAtom neg  x y \<in> S \<and> Member pos y e2 \<in> S \<longrightarrow> S \<union> {Member pos x e1, Member pos y e2} \<in> C) \<and>
              (\<forall> x y e. is_singleton (lang e) \<longrightarrow> Member pos x e \<in> S \<and> EqAtom pos x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y e} \<in> C) \<and> 
              (\<forall> x y e ec. is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> S \<and> EqAtom neg  x y \<in> S \<longrightarrow> S \<union> {Member pos x e, Member pos y ec} \<in> C) \<and> 
              (\<forall> x rs. length rs > 1 \<longrightarrow> empty_intersection_set rs \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r) ` (set rs)) \<notin> C) \<and> 
              (\<forall> x e fs. subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> S \<and> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C) \<and> 
              (\<forall> x e fs. eq_len_intersect e fs \<longrightarrow>  S \<union> ((\<lambda>r. Member pos x r)) ` (set fs) \<in> C \<longrightarrow> S \<union> {Member pos x e} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2. con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S \<longrightarrow> S \<union> {Member pos x e, EqAtom pos x (Conc x1 x2), Member pos x1 e1, Member pos x2 e2} \<in> C) \<and> 
              (\<forall> x x1 x2 e e1 e2. con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos (x1) e1 \<in> S \<and> Member pos (x2) e2 \<in> S \<longrightarrow> S \<union> {EqAtom pos x (Conc x1 x2), Member pos x e, Member pos (x1) e1, Member pos (x2) e2} \<in> C) \<and> 
              (\<forall> S'. S' = S \<longrightarrow> S' \<in> C))"

definition \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> one_sc_proof S' FF\<close>


lemma UN_finite_bound:
  assumes \<open>finite A\<close> and \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

lemma split_list:
  assumes \<open>x \<in> set A\<close>
  shows \<open>set (x # removeAll x A) = set A \<and> x \<notin> set (removeAll x A)\<close>
  using assms by auto


theorem consistent:
  assumes inf_param: \<open>infinite (UNIV::'a set)\<close>
  shows \<open>consistency {S:: (char BA) form set. \<exists>G. S = set G \<and> \<not> (\<stileturn> G)}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: \<open>(char BA) form set\<close>
  assume \<open>S \<in> {set G | G. \<not> (\<stileturn> G)}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G :: \<open>(char BA) form list\<close>
    where *: \<open>S = set G\<close> and \<open>\<not> (\<stileturn> G)\<close>
    by blast
  {
    fix A B 
    assume \<open>Con A B \<in> S\<close>
    then show "S \<union> {A, B} \<in> {set G |G. \<not> (\<stileturn> G)}"
      using * \<open>\<not> (\<stileturn> G)\<close> AlphaCon Order apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A B 
    assume \<open>form.Neg (Dis A B) \<in> S\<close>
    then show \<open> S \<union> {form.Neg A, form.Neg B} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaNegOr apply auto
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A B 
    assume \<open>Dis A B \<in> S\<close>
    then show \<open>S \<union> {A} \<in> {set G |G. \<not> (\<stileturn> G)} \<or> S \<union> {B} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaOr apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A B 
    assume \<open>form.Neg (Con A B) \<in> S\<close>
    then show \<open>S \<union> {form.Neg A} \<in> {set G |G. \<not> (\<stileturn> G)} \<or> S \<union> {form.Neg B} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaNegAnd apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix A
    assume \<open>form.Neg (form.Neg A) \<in> S\<close>
    then show \<open>S \<union> {A} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order AlphaNegNeg apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x e ec 
    assume \<open>regexp_compl e ec\<close> and \<open> Member neg x e \<in> S\<close>
    then show \<open>S \<union> {Member pos x ec} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NotMember apply auto
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x y p q 
    assume \<open>EqAtom neg x (Conc p q) \<in> S\<close>
    then show \<open>S \<union> {EqFresh neg x y, EqFresh pos y (Conc p q)} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NotEq apply auto
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x e ec
    assume \<open>regexp_compl e ec\<close> and \<open>S \<union> {Member pos x e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close> and\<open>S \<union> {Member pos x ec} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show \<open>S \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Cut 
      by blast 
  }
  {
    fix x y e
    assume \<open>Member pos x e \<in> S \<and> EqAtom pos x y \<in> S\<close>
    then show \<open>S \<union> {Member pos x e, EqAtom pos x y, Member pos y e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order EqProp apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix e1 e2 x y
    assume \<open>regexp_empty e1 e2\<close> and \<open>Member pos x e1 \<in> S \<and> EqAtom neg x y \<in> S \<and> Member pos y e2 \<in> S\<close>
    then show \<open>S \<union> {Member pos x e1, Member pos y e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NeqSubsume apply auto done
  }
  {
    fix x y e
    assume \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> and \<open>Member pos x e \<in> S \<and> EqAtom pos x y \<in> S\<close>
    then show \<open>S \<union> {Member pos x e, Member pos y e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order EqPropElim apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x y e ec
    assume \<open>is_singleton (Symbolic_Regular_Algebra_Model.lang e)\<close> and
       \<open>regexp_compl e ec\<close> and
       \<open>Member pos x e \<in> S \<and> EqAtom neg x y \<in> S\<close>
    then show \<open>S \<union> {Member pos x e, Member pos y ec} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order NeqPropElim apply auto 
      by (metis insert_absorb list.simps(15))
  }
  {
    fix x rs
    assume \<open> 1 < |rs|\<close> and \<open>empty_intersection_set rs\<close> and  \<open>S \<union> Member pos x ` set rs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show False
      using * \<open>\<not> (\<stileturn> G)\<close> Order Close apply auto 
      by (metis (no_types, lifting) list.set_map set_append sup_commute)
  }
  {
    fix x e fs
    assume \<open>subset_intersect_set e fs\<close> and \<open>Member pos x e \<in> S \<and> S \<union> Member pos x ` set fs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show \<open>S \<union> Member pos x ` set fs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Subsume apply auto done
  }
  {
    fix x e fs
    assume \<open>eq_len_intersect e fs\<close> and \<open>S \<union> Member pos x ` set fs \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
    then show \<open>S \<union> {Member pos x e} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Intersect apply auto 
      by (metis (no_types, lifting) list.set_map list.simps(15) set_append sup_commute)
  }
  {
    fix x x1 x2 e e1 e2
    assume \<open>con_fwd_prop e e1 e2\<close> and \<open>EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then have \<open>\<not> (\<stileturn> Member pos x e # EqAtom pos x (Conc x1 x2) # Member pos x1 e1# Member pos x2 e2 # G)\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_PropConc apply auto  
      by (smt (verit, del_insts) insert_absorb list.simps(15))
    moreover have \<open>S \<union> {Member pos x e,EqAtom pos x (Conc x1 x2),Member pos x1 e1, Member pos x2 e2} = set (Member pos x e # EqAtom pos x (Conc x1 x2) # Member pos x1 e1# Member pos x2 e2 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Member pos x e, EqAtom pos x (Conc x1 x2), Member pos x1 e1, Member pos x2 e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_PropConc by auto 
  }
  {
    fix S'
    assume \<open>S \<in> {set G |G. \<not> (\<stileturn> G)}\<close> and \<open>S' = S\<close>
    then show \<open>S' \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using \<open>\<not> (\<stileturn> G)\<close> by auto
  }
  {
    fix x x1 x2 e e1 e2 
    assume \<open>con_fwd_prop_elim e e1 e2\<close> and \<open>EqAtom pos x (Conc x1 x2) \<in> S \<and> Member pos x1 e1 \<in> S \<and> Member pos x2 e2 \<in> S\<close>
    then have \<open>\<not> (\<stileturn> EqAtom pos x (Conc x1 x2) # Member pos x e# Member pos x1 e1#  Member pos x2 e2 # G)\<close>
      using * \<open>\<not> (\<stileturn> G)\<close> Order Fwd_ElimConc apply auto 
      by (smt (verit, del_insts) insert_absorb list.set_intros(2) list.simps(15))
    moreover have \<open>S \<union> {EqAtom pos x (Conc x1 x2), Member pos x e, Member pos x1 e1,  Member pos x2 e2} = set (EqAtom pos x (Conc x1 x2) # Member pos x e# Member pos x1 e1#  Member pos x2 e2 # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {EqAtom pos x (Conc x1 x2), Member pos x e, Member pos x1 e1, Member pos x2 e2} \<in> {set G |G. \<not> (\<stileturn> G)}\<close>
      using \<open>\<not> (\<stileturn> G)\<close> by auto 
  }
qed


subsection \<open>Enumerating datatypes\<close>

instance \<open>rexp\<close> :: (countable) countable
  by countable_datatype

instance \<open>tm\<close> ::  countable
  by countable_datatype

instance \<open>sign\<close> :: countable
  by countable_datatype

instance form :: (countable) countable 
  by countable_datatype
  
subsection \<open>Extension to maximal consistent set\<close>

subsection \<open>Hintikka sets and Herbrand models\<close>

text \<open>
\label{sec:hintikka}
A Hintikka set is defined as follows:
\<close>

locale hintikka = 
  fixes H :: \<open>(char BA) form set\<close>
  assumes 
  Basic: \<open>\<not> (A \<in> H \<and> Neg A \<in> H)\<close> and
  FF: \<open>FF \<notin> H\<close> and
  TT: \<open>Neg TT \<notin> H\<close> and
  NegNeg : \<open>(Neg (Neg Z) \<in> H \<longrightarrow> Z \<in> H)\<close> and 
  Con: \<open>Con A B \<in> H \<longrightarrow> A \<in> H \<and> B \<in> H\<close> and
  NDis : \<open>Neg (Dis A B) \<in> H \<longrightarrow> Neg A \<in> H \<and> Neg B \<in> H\<close> and
  Dis: \<open>Dis A B \<in> H \<longrightarrow> A \<in> H \<or> B \<in> H\<close> and
  NCon:\<open>Neg (Con A B) \<in> H \<longrightarrow> Neg A \<in> H \<or> Neg B \<in> H\<close> and
 NMember: \<open>regexp_compl e ec \<longrightarrow> Member neg x e \<in> H \<longrightarrow> Member pos x ec \<in> H\<close> and 
 NEq: \<open>EqAtom neg x (Conc x1 x2) \<in> H \<longrightarrow> EqFresh neg x y \<in> H \<and> EqFresh pos y (Conc x1 x2) \<in> H\<close> and
 Cut: \<open>regexp_compl e ec \<longrightarrow> Member pos x e \<in> H \<or> Member pos x ec \<in> H\<close> and 
 EProp: \<open>Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<and> Member pos y e \<in> H\<close> and
 NSubsume: \<open>regexp_empty e1 e2 \<longrightarrow> Member pos x e1 \<in> H \<and> EqAtom neg  x y \<in> H \<and> Member pos y e2 \<in> H \<longrightarrow> Member pos x e1 \<in> H \<and> Member pos y e2 \<in> H\<close> and
 EPropElim: \<open>is_singleton (lang e) \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> Member pos y e \<in> H\<close> and 
 NPropElim: \<open>is_singleton (lang e) \<longrightarrow> regexp_compl e ec \<longrightarrow> Member pos x e \<in> H \<and> EqAtom neg  x y \<in> H \<longrightarrow> Member pos x e \<in> H \<and> Member pos y ec \<in> H\<close> and 
 Close: \<open>length rs > 1 \<longrightarrow> empty_intersection_set rs \<longrightarrow> ((\<lambda>r. Member pos x r) ` (set rs)) \<subseteq> H\<close> and 
 Subsumer:    \<open>subset_intersect_set e fs \<longrightarrow> Member pos x e \<in> H \<and> ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H \<longrightarrow> ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H\<close> and 
 Intersect:    \<open>eq_len_intersect e fs \<longrightarrow>  ((\<lambda>r. Member pos x r)) ` (set fs) \<subseteq> H \<longrightarrow> Member pos x e \<in> H\<close> and 
 Con_fwd_prop: \<open>con_fwd_prop e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos x1 e1 \<in> H \<and> Member pos x2 e2 \<in> H \<longrightarrow> Member pos x e \<in> H \<and> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos x1 e1 \<in> H \<and> Member pos x2 e2 \<in> H\<close> and 
 Con_fwd_prop_elim: \<open>(con_fwd_prop_elim e e1 e2 \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos (x1) e1 \<in> H \<and> Member pos (x2) e2 \<in> H \<longrightarrow> EqAtom pos x (Conc x1 x2) \<in> H \<and> Member pos x e \<in> H \<and> Member pos (x1) e1 \<in> H \<and> Member pos (x2) e2 \<in> H)\<close>

subsection \<open>Model existence theorem\<close>

subsection \<open>Completeness for Natural Deduction\<close>

theorem One_SC_completeness':
  fixes p :: \<open>(char BA) form\<close>
  assumes  mod: \<open>\<forall>(e :: nat \<Rightarrow> string) f. list_all (eval e f) ps \<longrightarrow> eval e f p\<close>
  shows \<open>one_sc_proof ps p\<close>
  sorry


end