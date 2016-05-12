theory Abstract_Formula
imports
  Main
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Stream"
  Indexed_FSet
begin
locale Abstract_Formulas =
  fixes freshenV :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
  fixes rename :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
  fixes fv :: "'form \<Rightarrow> 'var set"
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  fixes ran_fv :: "'subst \<Rightarrow> 'var set"
  fixes anyP :: "'form"
  assumes freshenV_eq_iff[simp]: "freshenV a v = freshenV a' v' \<longleftrightarrow> a = a' \<and> v = v'"
  assumes fv_rename: "fv (rename p f) = p ` fv f"
  assumes rename_closed: "fv f = {} \<Longrightarrow> rename p f = f"
  assumes subst_closed: "fv f = {} \<Longrightarrow> subst s f = f"
  assumes fv_subst: "fv (subst s f) \<subseteq> fv f \<union> ran_fv s"
  assumes anyP_is_any': "\<exists> s. subst s (rename (freshenV a) anyP) = f"
begin
  definition freshen :: "nat \<Rightarrow> 'form \<Rightarrow> 'form" where
    "freshen n = rename (freshenV n)"

  lemma fv_freshen: "fv (freshen a f) = freshenV a ` fv f"
    unfolding freshen_def by (rule fv_rename)

  lemma anyP_is_any: "\<exists> s. subst s (freshen a anyP) = f"
    unfolding freshen_def by (rule anyP_is_any')

  definition closed :: "'form \<Rightarrow> bool" where "closed f \<longleftrightarrow> fv f = {}"
  lemma closed_fv: "closed f \<Longrightarrow> fv f = {}" unfolding closed_def by auto

  lemma closed_eq:
    assumes "closed f1"
    assumes "closed f2"
    shows "subst s1 (freshen a1 f1) = subst s2 (freshen a2 f2) \<longleftrightarrow> f1 = f2"
  using assms
    by (auto simp add: closed_def freshen_def fv_freshen subst_closed rename_closed)

  lemma freshenV_range_eq_iff[simp]: "freshenV a v \<in> range (freshenV a') \<longleftrightarrow> a = a'"
    by auto
end

datatype ('form, 'var) antecedent =
  Antecedent (a_hyps: "'form fset") (a_conc: "'form") (a_fresh: "'var set")

abbreviation plain_ant :: "'form \<Rightarrow> ('form, 'var) antecedent"
  where "plain_ant f \<equiv> Antecedent {||} f {}"

locale Abstract_Rules =
  Abstract_Formulas freshenV rename fv subst ran_fv anyP
  for freshenV :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
  and rename  :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
  and fv :: "'form \<Rightarrow> 'var set"
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and ran_fv :: "'subst \<Rightarrow> 'var set" 
  and anyP :: "'form" +
  fixes antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list"
  fixes consequent :: "'rule \<Rightarrow> 'form list"
  and rules :: "'rule stream"
begin
  definition f_antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent fset"
    where "f_antecedent r = fset_from_list (antecedent r)"
  definition "f_consequent r = fset_from_list (consequent r)"
end

locale Abstract_Task =
  Abstract_Rules freshenV rename fv subst ran_fv anyP  antecedent consequent rules
  for freshenV :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
    and rename  :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
    and fv :: "'form \<Rightarrow> 'var set"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and ran_fv :: "'subst \<Rightarrow> 'var set" 
    and anyP :: "'form"
    and antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list"
    and consequent :: "'rule \<Rightarrow> 'form list" 
    and rules :: "'rule stream" +
  fixes assumptions :: "'form list"
  fixes conclusions :: "'form list"
  assumes assumptions_closed: "\<And> a. a \<in> set assumptions \<Longrightarrow> closed a"
  assumes conclusions_closed: "\<And> c. c \<in> set conclusions \<Longrightarrow> closed c"
  assumes no_empty_conclusions: "\<forall>xs\<in>sset rules. consequent xs \<noteq> []"
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
      by (simp add: closed_fv freshen_def rename_closed subst_closed)

  lemma subst_freshen_conclusions[simp]:
    assumes "pf \<in> set conclusions"
    shows "subst s (freshen a pf) = pf "
      using assms conclusions_closed 
      by (simp add: closed_fv freshen_def rename_closed subst_closed)

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