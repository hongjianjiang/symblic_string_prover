chapter \<open>The prover\<close>

section \<open>Proof search procedure\<close>

theory Prover
  imports Main 
begin 

text \<open>This theory defines the actual proof search procedure.\<close>

subsection \<open>Datatypes\<close>

text \<open>A sequent is a list of formulas
type_synonym sequent = \<open>fm list\<close>\<close>

text \<open>We introduce a number of rules to prove sequents.\<close>

datatype rule = 
    AlphaDis      | AlphaCon
  | NotMember     | NonEqual
  | Cut           | EqProp
  | NotEqSub      | EqPropElim
  | NotEqPropElim | Close
  | Subsume       | Intersect
  | FwdProp       | FwdPropElim
  | BwdProp       | NegNeg
  



end