theory Abstract_Formula
imports
  Main
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Stream"
  Indexed_FSet
begin
locale Abstract_Formulas =
  fixes freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
  fixes renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
  fixes lconsts :: "'form \<Rightarrow> 'var set"
  fixes closed :: "'form \<Rightarrow> bool"
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  fixes subst_lconsts :: "'subst \<Rightarrow> 'var set"
  fixes subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
  fixes anyP :: "'form"
  assumes freshenLC_eq_iff[simp]: "freshenLC a v = freshenLC a' v' \<longleftrightarrow> a = a' \<and> v = v'"
  assumes lconsts_renameLCs: "lconsts (renameLCs p f) = p ` lconsts f"
  assumes rename_closed: "lconsts f = {} \<Longrightarrow> renameLCs p f = f"
  assumes subst_closed: "closed f \<Longrightarrow> subst s f = f"
  assumes closed_no_lconsts: "closed f \<Longrightarrow> lconsts f = {}"
  assumes fv_subst: "lconsts (subst s f) \<subseteq> lconsts f \<union> subst_lconsts s"
  assumes rename_rename: "renameLCs p1 (renameLCs p2 f) = renameLCs (p1 \<circ> p2) f"
  assumes rename_subst: "renameLCs p (subst s f) = subst (subst_renameLCs p s) (renameLCs p f)"
  assumes renameLCs_cong: "(\<And> x. x \<in> lconsts f \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> renameLCs f1 f = renameLCs f2 f"
  assumes subst_renameLCs_cong: "(\<And> x. x \<in> subst_lconsts s \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> subst_renameLCs f1 s = subst_renameLCs f2 s"
  assumes subst_lconsts_subst_renameLCs: "subst_lconsts (subst_renameLCs p s) = p ` subst_lconsts s"
  assumes lconsts_anyP: "lconsts anyP = {}"
  assumes empty_subst: "\<exists> s. (\<forall> f. subst s f = f) \<and> subst_lconsts s = {}"
  assumes anyP_is_any: "\<exists> s. subst s anyP = f"
begin
  definition freshen :: "nat \<Rightarrow> 'form \<Rightarrow> 'form" where
    "freshen n = renameLCs (freshenLC n)"

  definition empty_subst :: "'subst" where
    "empty_subst = (SOME s. (\<forall> f. subst s f = f) \<and> subst_lconsts s = {})"

  lemma empty_subst_spec:
    "(\<forall> f. subst empty_subst f = f) \<and> subst_lconsts empty_subst = {}"
    unfolding empty_subst_def using empty_subst by (rule someI_ex)
  lemma subst_empty_subst[simp]: "subst empty_subst f = f"
    by (metis empty_subst_spec)
  lemma subst_lconsts_empty_subst[simp]: "subst_lconsts empty_subst = {}"
    by (metis empty_subst_spec)

  lemma lconsts_freshen: "lconsts (freshen a f) = freshenLC a ` lconsts f"
    unfolding freshen_def by (rule lconsts_renameLCs)

  lemma freshen_closed: "lconsts f = {} \<Longrightarrow> freshen a f = f"
    unfolding freshen_def by (rule rename_closed)
    
  lemma closed_eq:
    assumes "closed f1"
    assumes "closed f2"
    shows "subst s1 (freshen a1 f1) = subst s2 (freshen a2 f2) \<longleftrightarrow> f1 = f2"
  using assms
    by (auto simp add: closed_no_lconsts freshen_def lconsts_freshen subst_closed rename_closed)

  lemma freshenLC_range_eq_iff[simp]: "freshenLC a v \<in> range (freshenLC a') \<longleftrightarrow> a = a'"
    by auto

  definition rerename :: "'var set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('var \<Rightarrow> 'var) \<Rightarrow> ('var \<Rightarrow> 'var)" where
    "rerename V from to f x = (if x \<in> freshenLC from ` V then freshenLC to (inv (freshenLC from) x) else f x)"
  
  lemma inj_freshenLC[simp]: "inj (freshenLC i)"
    by (rule injI) simp
  
  lemma rerename_freshen[simp]: "x \<in> V \<Longrightarrow> rerename  V i (isidx is) f (freshenLC i x) = freshenLC (isidx is) x"
    unfolding rerename_def by simp

  (*
  lemma range_rerename_eq: "range (rerename V from to f) = freshenLC to ` V \<union> (range f - freshenLC from ` V)"
    apply (auto simp add: rerename_def split: if_splits)
    sledgehammer
  *)
  
  lemma range_rerename: "range (rerename V  from to f) \<subseteq> freshenLC to ` V \<union> range f"
    by (auto simp add: rerename_def split: if_splits)

  lemma rerename_noop:
      "x \<notin> freshenLC from ` V  \<Longrightarrow> rerename V from to f x = f x"
    by (auto simp add: rerename_def split: if_splits)

  lemma rerename_rename_noop:
      "freshenLC from ` V \<inter> lconsts form  = {}  \<Longrightarrow> renameLCs (rerename V from to f) form = renameLCs f form"
      by (intro renameLCs_cong rerename_noop) auto

  lemma rerename_subst_noop:
      "freshenLC from ` V \<inter> subst_lconsts s  = {}  \<Longrightarrow> subst_renameLCs (rerename V from to f) s = subst_renameLCs f s"
      by (intro subst_renameLCs_cong rerename_noop) auto
end

datatype ('form, 'var) antecedent =
  Antecedent (a_hyps: "'form fset") (a_conc: "'form") (a_fresh: "'var set")

abbreviation plain_ant :: "'form \<Rightarrow> ('form, 'var) antecedent"
  where "plain_ant f \<equiv> Antecedent {||} f {}"

locale Abstract_Rules =
  Abstract_Formulas freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP
  for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
  and renameLCs  :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
  and lconsts :: "'form \<Rightarrow> 'var set"
  and closed :: "'form \<Rightarrow> bool"
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
  and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
  and anyP :: "'form" +
  fixes antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list"
  fixes consequent :: "'rule \<Rightarrow> 'form list"
  and rules :: "'rule stream"
  assumes no_empty_conclusions: "\<forall>xs\<in>sset rules. consequent xs \<noteq> []"
begin
  definition f_antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent fset"
    where "f_antecedent r = fset_from_list (antecedent r)"
  definition "f_consequent r = fset_from_list (consequent r)"
end

locale Abstract_Task =
  Abstract_Rules freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP  antecedent consequent rules
  for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
    and renameLCs  :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
    and lconsts :: "'form \<Rightarrow> 'var set"
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form"
    and antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list"
    and consequent :: "'rule \<Rightarrow> 'form list" 
    and rules :: "'rule stream" +
  fixes assumptions :: "'form list"
  fixes conclusions :: "'form list"
  assumes assumptions_closed: "\<And> a. a \<in> set assumptions \<Longrightarrow> closed a"
  assumes conclusions_closed: "\<And> c. c \<in> set conclusions \<Longrightarrow> closed c"
begin
  definition ass_forms where "ass_forms = fset_from_list assumptions"
  definition conc_forms where "conc_forms = fset_from_list  conclusions"

  lemma mem_ass_forms[simp]: "a |\<in>| ass_forms \<longleftrightarrow> a \<in> set assumptions"
    by (auto simp add: ass_forms_def)
  
  lemma mem_conc_forms[simp]: "a |\<in>| conc_forms \<longleftrightarrow> a \<in> set conclusions"
    by (auto simp add: conc_forms_def)

  lemma subst_freshen_assumptions[simp]:
    assumes "pf \<in> set assumptions"
    shows "subst s (freshen a pf) = pf "
      using assms assumptions_closed 
      by (simp add: closed_no_lconsts freshen_def rename_closed subst_closed)

  lemma subst_freshen_conclusions[simp]:
    assumes "pf \<in> set conclusions"
    shows "subst s (freshen a pf) = pf "
      using assms conclusions_closed 
      by (simp add: closed_no_lconsts freshen_def rename_closed subst_closed)

  lemma subst_freshen_in_ass_formsI:
    assumes "pf \<in> set assumptions"
    shows "subst s (freshen a pf) |\<in>| ass_forms"
      using assms by simp

  lemma subst_freshen_in_conc_formsI:
    assumes "pf \<in> set conclusions"
    shows "subst s (freshen a pf) |\<in>| conc_forms"
      using assms by simp
end

end