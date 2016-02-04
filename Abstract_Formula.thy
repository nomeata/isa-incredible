theory Abstract_Formula
imports
  Main
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Stream"
begin

context includes fset.lifting
begin
lift_definition fset_from_list :: "'a list => 'a fset" is set by (rule finite_set)
lemma mem_fset_from_list[simp]: "x |\<in>| fset_from_list l  \<longleftrightarrow> x \<in> set l" by transfer rule
lemma fimage_fset_from_list[simp]: "f |`| fset_from_list l = fset_from_list (map f l)"  by transfer auto
lemma fset_fset_from_list[simp]: "fset (fset_from_list l) = set l"  by transfer auto
end

locale Abstract_Formulas =
  fixes freshen :: "'annot \<Rightarrow> 'preform \<Rightarrow> 'form"
  fixes pre_fv :: "'preform \<Rightarrow> 'var set"
  fixes fv :: "'form \<Rightarrow> ('var \<times> 'annot) set"
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  fixes ran_fv :: "'subst \<Rightarrow> ('var \<times> 'annot) set"
  fixes closed :: "'preform \<Rightarrow> bool"
  assumes annotate_preserves_fv: "fst ` fv (freshen a pf) = pre_fv pf"
  assumes fv_subst: "fv (subst s f) \<subseteq> ran_fv s"
  assumes closed_eq: "closed pf \<Longrightarrow> subst s1 (freshen a1 pf) = subst s2 (freshen a2 pf)"

datatype ('preform, 'var) antecedent =
  Antecedent (a_hyps: "'preform fset") (a_conc: "'preform") (a_fresh: "'var set")

abbreviation plain_ant :: "'preform \<Rightarrow> ('preform, 'var) antecedent"
  where "plain_ant f \<equiv> Antecedent {||} f {}"

locale Abstract_Rules =
  Abstract_Formulas freshen pre_fv fv subst
  for freshen :: "'annot \<Rightarrow> 'preform \<Rightarrow> 'form"
  and pre_fv :: "'preform \<Rightarrow> 'var set"
  and fv :: "'form \<Rightarrow> ('var \<times> 'annot) set"
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" +
  fixes antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent list"
  fixes consequent :: "'rule \<Rightarrow> 'preform list"
  and rules :: "'rule stream"
begin
  definition f_antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent fset"
    where "f_antecedent r = fset_from_list (antecedent r)"
  definition "f_consequent r = fset_from_list (consequent r)"
end

locale Abstract_Task =
  Abstract_Rules ran_fv closed freshen pre_fv fv subst antecedent consequent rules
  for  ran_fv :: "'subst \<Rightarrow> ('var \<times> 'annot) set" 
    and closed :: "'preform \<Rightarrow> bool" 
    and freshen :: "'annot \<Rightarrow> 'preform \<Rightarrow> 'form" 
    and pre_fv :: "'preform \<Rightarrow> 'var set" 
    and fv :: "'form \<Rightarrow> ('var \<times> 'annot) set" 
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
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