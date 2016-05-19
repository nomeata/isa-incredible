theory Incredible_Propositional imports
  Natural_Deduction
  Abstract_Rules_To_Incredible
begin

class infinite =
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

instance nat :: infinite
  by (intro_classes) simp
instance prod :: (infinite, type) infinite
  by intro_classes (simp add: finite_prod infinite_UNIV)
instance list :: (type) infinite
  by intro_classes (simp add: infinite_UNIV_listI)

datatype ('var,'cname) pform =
    Var "'var::{countable,infinite}"
  | Const (name:'cname) (params: "('var,'cname) pform list")

fun subst :: "('var::{countable,infinite} \<Rightarrow> ('var,'cname) pform) \<Rightarrow> ('var,'cname) pform \<Rightarrow> ('var,'cname) pform"
  where "subst s (Var v) = s v"
  | "subst s (Const n ps) = Const n (map (subst s) ps)"

fun closed :: "('var::{countable,infinite},'cname) pform \<Rightarrow> bool"
  where "closed (Var v) \<longleftrightarrow> False"
  | "closed (Const n ps) \<longleftrightarrow> list_all closed ps"

lemma countable_infinite_ex_bij: "\<exists>f::('a::{countable,infinite}\<Rightarrow>'b::{countable,infinite}). bij f"
proof -
  note [[show_consts, show_types]]
  have "infinite (range (to_nat::'a \<Rightarrow> nat))"
    using finite_imageD infinite_UNIV by blast
  moreover have "infinite (range (to_nat::'b \<Rightarrow> nat))"
    using finite_imageD infinite_UNIV by blast
  ultimately have "\<exists>f. bij_betw f (range (to_nat::'a \<Rightarrow> nat)) (range (to_nat::'b \<Rightarrow> nat))"
    by (meson bij_betw_inv bij_betw_trans bij_enumerate)
  then obtain f where f_def: "bij_betw f (range (to_nat::'a \<Rightarrow> nat)) (range (to_nat::'b \<Rightarrow> nat))" ..
  then have f_range_trans: "f ` (range (to_nat::'a \<Rightarrow> nat)) = range (to_nat::'b \<Rightarrow> nat)"
    unfolding bij_betw_def by simp
  have "surj ((from_nat::nat \<Rightarrow> 'b) \<circ> f \<circ> (to_nat::'a \<Rightarrow> nat))"
  proof (rule surjI)
    fix a
    obtain b where [simp]: "to_nat (a::'b) = b" by blast
    hence "b \<in> range (to_nat::'b \<Rightarrow> nat)" by blast
    with f_range_trans have "b \<in> f ` (range (to_nat::'a \<Rightarrow> nat))" by simp
    from imageE [OF this] obtain c where [simp]:"f c = b" and "c \<in> range (to_nat::'a \<Rightarrow> nat)"
      by auto
    with f_def have [simp]: "inv_into (range (to_nat::'a \<Rightarrow> nat)) f b = c"
      by (meson bij_betw_def inv_into_f_f)
    then obtain d where cd: "from_nat c = (d::'a)" by blast
    with \<open>c \<in> range to_nat\<close> have [simp]:"to_nat d = c" by auto
    from \<open>to_nat a = b\<close> have [simp]: "from_nat b = a"
      using from_nat_to_nat by blast
    show "(from_nat \<circ> f \<circ> to_nat) (((from_nat::nat \<Rightarrow> 'a) \<circ> inv_into (range (to_nat::'a \<Rightarrow> nat)) f \<circ> (to_nat::'b \<Rightarrow> nat)) a) = a"
      by (clarsimp simp: cd)
  qed
  moreover have "inj ((from_nat::nat \<Rightarrow> 'b) \<circ> f \<circ> (to_nat::'a \<Rightarrow> nat))"
    apply (rule injI)
    apply auto
    by (metis bij_betw_inv_into_left f_def f_inv_into_f f_range_trans from_nat_def image_eqI rangeI to_nat_split)
  ultimately show ?thesis by (blast intro: bijI)
qed
  

interpretation propositional: Abstract_Formulas
  "curry (SOME f. bij f):: nat \<Rightarrow> 'var \<Rightarrow> 'var"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: ('var::{countable,infinite},'cname) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
proof
  fix a v a' v'
  from countable_infinite_ex_bij obtain f where "bij (f::nat \<times> 'var \<Rightarrow> 'var)" by blast
  then show "(curry (SOME f. bij (f::nat \<times> 'var \<Rightarrow> 'var)) (a::nat) (v::'var) = curry (SOME f. bij f) (a'::nat) (v'::'var)) =
       (a = a' \<and> v = v')"
  apply (rule someI2 [where Q="\<lambda>f. curry f a v = curry f a' v' \<longleftrightarrow> a = a' \<and> v = v'"])
  by auto (metis bij_pointE prod.inject)+
next
  fix f s
  assume "closed (f::('var, 'cname) pform)"
  then show "subst s f = f"
  proof (induction s f rule: subst.induct)
    case (2 s n ps)
    thus ?case by (induction ps) auto
  qed auto
next
  have "subst Var f = f" for f :: "('var,'cname) pform"
    by (induction f) (auto intro: map_idI)
  then show "\<exists>s. (\<forall>f. subst s (f::('var,'cname) pform) = f) \<and> {} = {}"
    by (rule_tac x=Var in exI; clarsimp)
qed auto

declare Incredible_Propositional.propositional.subst_lconsts_empty_subst [simp del]


datatype prop_funs = "and" | imp | C "string"

datatype prop_rule = andI | andE | impI | impE

definition prop_rules :: "prop_rule stream"
  where "prop_rules = cycle [andI, andE, impI, impE]"

lemma sset_cycle [simp]: "sset (cycle xs) = set xs"
  sorry

lemma iR_prop_rules [simp]: "i.R prop_rules = {andI, andE, impI, impE}"
  unfolding prop_rules_def by simp

abbreviation X :: "(string,'a) pform"
  where "X \<equiv> Var ''X''"
abbreviation Y :: "(string,'a) pform"
  where "Y \<equiv> Var ''Y''"

fun consequent :: "prop_rule \<Rightarrow> (string, prop_funs) pform list"
  where "consequent andI = [Const and [X, Y]]"
  | "consequent andE = [X, Y]"
  | "consequent impI = [Const imp [X, Y]]"
  | "consequent impE = [Y]"

fun antecedent :: "prop_rule \<Rightarrow> ((string,prop_funs) pform,string) antecedent list"
  where "antecedent andI = [Antecedent {||} X {}, Antecedent {||} Y {}]"
  | "antecedent andE = [Antecedent {||} (Const and [X, Y]) {}]"
  | "antecedent impI = [Antecedent {|X|} Y {}]"
  | "antecedent impE = [Antecedent {||} (Const imp [X, Y]) {}, Antecedent {||} X {}]"


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

interpretation task1_1: Abstract_Task
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
  "[Const (C ''A'') []]"
  "[Const (C ''A'') []]"
by unfold_locales simp

lemma "task1_1.solved"
  unfolding task1_1.solved_def
apply clarsimp
apply (rule_tac x="{|Const (C ''A'') []|}" in exI)
apply clarsimp
apply (rule_tac x="Node ({|Const (C ''A'') []|} \<turnstile> Const (C ''A'') [], Axiom) {||}" in exI)
apply clarsimp
apply (rule conjI)
 apply (rule task1_1.wf)
   apply clarsimp
  apply clarsimp
  apply (rule task1_1.eff.intros(1))
  apply simp
 apply clarsimp
by (auto intro: tfinite.intros)

print_locale Vertex_Graph

interpretation task1_1: Vertex_Graph task1_1.nodes task1_1.inPorts task1_1.outPorts "{|0::nat,1|}"
  "undefined(0 := Assumption (Const (C ''A'') []), 1 := Conclusion (Const (C ''A'') []))"
.

declare One_nat_def [simp del]

interpretation Tasked_Proof_Graph
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
  "[Const (C ''A'') []]"
  "[Const (C ''A'') []]"
  "{|0::nat,1|}"
  "undefined(0 := Assumption (Const (C ''A'') []), 1 := Conclusion (Const (C ''A'') []))"
  "{((0,Reg (Const (C ''A'') [])),(1,plain_ant (Const (C ''A'') [])))}"
  "id"
  "undefined"
apply unfold_locales
         apply simp
        apply clarsimp
       apply clarsimp
      apply clarsimp
sorry

end
