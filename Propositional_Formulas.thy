theory Propositional_Formulas
imports
  Abstract_Formula
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/Library/Infinite_Set"
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

declare Propositional_Formulas.propositional.subst_lconsts_empty_subst [simp del]

end