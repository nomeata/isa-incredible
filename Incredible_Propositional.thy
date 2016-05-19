theory Incredible_Propositional imports
  Natural_Deduction
  Abstract_Rules_To_Incredible
  Propositional_Formulas
begin


datatype prop_funs = "and" | imp | Const "string"

datatype prop_rule = andI | andE | impI | impE

definition prop_rules :: "prop_rule stream"
  where "prop_rules = cycle [andI, andE, impI, impE]"

lemma sset_cycle [simp]:
  assumes "xs \<noteq> []" 
  shows "sset (cycle xs) = set xs"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> sset (cycle xs)"
  from this assms show "x \<in> set xs"
    by (induction "cycle xs" arbitrary: xs rule: sset_induct) (case_tac xs; fastforce)+
next
  fix x
  assume "x \<in> set xs"
  with assms show "x \<in> sset (cycle xs)"
    by (metis UnI1 cycle_decomp sset_shift)
qed

lemma iR_prop_rules [simp]: "i.R prop_rules = {andI, andE, impI, impE}"
  unfolding prop_rules_def by simp

abbreviation X :: "(string,'a) pform"
  where "X \<equiv> Var ''X''"
abbreviation Y :: "(string,'a) pform"
  where "Y \<equiv> Var ''Y''"

fun consequent :: "prop_rule \<Rightarrow> (string, prop_funs) pform list"
  where "consequent andI = [Fun and [X, Y]]"
  | "consequent andE = [X, Y]"
  | "consequent impI = [Fun imp [X, Y]]"
  | "consequent impE = [Y]"

fun antecedent :: "prop_rule \<Rightarrow> ((string,prop_funs) pform,string) antecedent list"
  where "antecedent andI = [Antecedent {||} X {}, Antecedent {||} Y {}]"
  | "antecedent andE = [Antecedent {||} (Fun and [X, Y]) {}]"
  | "antecedent impI = [Antecedent {|X|} Y {}]"
  | "antecedent impE = [Antecedent {||} (Fun imp [X, Y]) {}, Antecedent {||} X {}]"


interpretation propositional: Abstract_Rules
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
proof
  show "\<forall>xs\<in>i.R prop_rules. consequent xs \<noteq> []"
    unfolding prop_rules_def
    using consequent.elims by blast
next
  show "\<forall>xs\<in>i.R prop_rules. \<Union>((\<lambda>_. {}) ` set (consequent xs)) = {}"
    by clarsimp
next
  fix i' r i ia
  assume "r \<in> i.R prop_rules"
    and "ia < length (antecedent r)"
    and "i' < length (antecedent r)"
  then show "a_fresh (antecedent r ! ia) \<inter> a_fresh (antecedent r ! i') = {} \<or> ia = i'"
    by (cases i'; auto)
next
  fix p
  show "{} \<union> \<Union>((\<lambda>_. {}) ` fset (a_hyps p)) \<subseteq> a_fresh p"  by clarsimp
qed

end
