theory Abstract_Formula
imports
  Main
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Stream"
  Indexed_FSet
begin

type_synonym 'a annotated = "('a \<times> nat)"

locale Abstract_Formulas =
  fixes freshen :: "nat \<Rightarrow> 'preform \<Rightarrow> 'form"
  fixes pre_fv :: "'preform \<Rightarrow> 'var set"
  fixes fv :: "'form \<Rightarrow> 'var annotated set"
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  fixes ran_fv :: "'subst \<Rightarrow> 'var annotated set"
  fixes closed :: "'preform \<Rightarrow> bool"
  fixes anyP :: "'preform"
  assumes fv_freshen': "fv (freshen a pf) = (\<lambda> v. (v,a)) ` pre_fv pf"
  assumes subst_no_vars: "pre_fv pf = {} \<Longrightarrow> fv (subst s f) = {}"
  assumes fv_subst: "fv (subst s f) \<subseteq> fv f \<union> ran_fv s"
  assumes closed_pre_fv: "closed pf \<Longrightarrow> pre_fv pf = {}"
  assumes closed_eq: "closed pf \<Longrightarrow> subst s1 (freshen a1 pf) = subst s2 (freshen a2 pf)"
  assumes anyP_is_any: "\<exists> s. subst s (freshen a anyP) = f"
begin
  definition freshenV :: "nat \<Rightarrow> 'var \<Rightarrow>  'var annotated" where "freshenV a v = (v,a)"
  lemma fv_freshen: "fv (freshen a pf) = freshenV a ` pre_fv pf"
    using freshenV_def fv_freshen' by auto
  lemma freshenV_eq_iff: "freshenV a v = freshenV a' v' \<longleftrightarrow> a = a' \<and> v = v'"
    by (auto simp add: freshenV_def)

end

datatype ('preform, 'var) antecedent =
  Antecedent (a_hyps: "'preform fset") (a_conc: "'preform") (a_fresh: "'var set")

abbreviation plain_ant :: "'preform \<Rightarrow> ('preform, 'var) antecedent"
  where "plain_ant f \<equiv> Antecedent {||} f {}"

locale Abstract_Rules =
  Abstract_Formulas freshen pre_fv fv subst ran_fv closed anyP
  for freshen :: "nat \<Rightarrow> 'preform \<Rightarrow> 'form"
  and pre_fv :: "'preform \<Rightarrow> 'var set"
  and fv :: "'form \<Rightarrow> 'var annotated set"
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and ran_fv :: "'subst \<Rightarrow> ('var \<times> nat) set" 
  and closed :: "'preform \<Rightarrow> bool" 
  and anyP :: "'preform" +
  fixes antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent list"
  fixes consequent :: "'rule \<Rightarrow> 'preform list"
  and rules :: "'rule stream"
begin
  definition f_antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent fset"
    where "f_antecedent r = fset_from_list (antecedent r)"
  definition "f_consequent r = fset_from_list (consequent r)"
end

locale Abstract_Task =
  Abstract_Rules freshen pre_fv fv subst ran_fv closed anyP  antecedent consequent rules
  for freshen :: "nat \<Rightarrow> 'preform \<Rightarrow> 'form" 
    and pre_fv :: "'preform \<Rightarrow> 'var set" 
    and fv :: "'form \<Rightarrow> 'var annotated set" 
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and ran_fv :: "'subst \<Rightarrow> 'var annotated set" 
    and closed :: "'preform \<Rightarrow> bool" 
    and anyP :: "'preform" 
    and antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent list"
    and consequent :: "'rule \<Rightarrow> 'preform list" 
    and rules :: "'rule stream" +
  fixes assumptions :: "'preform list"
  fixes conclusions :: "'preform list"
  assumes assumptions_closed: "\<forall>a \<in> set assumptions. closed a"
  assumes conclusions_closed: "\<forall>c \<in> set conclusions. closed a"
  assumes no_empty_conclusions: "\<forall>xs\<in>sset rules. consequent xs \<noteq> []"
begin
  definition ass_forms where "ass_forms = fset_from_list (map (subst undefined) (map (freshen undefined) assumptions))"
  definition conc_forms where "conc_forms = fset_from_list (map (subst undefined) (map (freshen undefined) conclusions))"

  lemma subst_freshen_in_ass_formsI:
    assumes "pf \<in> set assumptions"
    shows "subst s (freshen a pf) |\<in>| ass_forms"
      using assms ass_forms_def assumptions_closed closed_eq by fastforce

  lemma subst_freshen_in_conc_formsI:
    assumes "pf \<in> set conclusions"
    shows "subst s (freshen a pf) |\<in>| conc_forms"
      using assms conc_forms_def conclusions_closed closed_eq by fastforce
end

end