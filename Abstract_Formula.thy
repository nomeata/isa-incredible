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
  fixes annotate :: "'annot \<Rightarrow> 'preform \<Rightarrow> 'form"
  fixes pre_fv :: "'preform \<Rightarrow> 'var set"
  fixes fv :: "'form \<Rightarrow> ('var \<times> 'annot) set"
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  fixes ran_fv :: "'subst \<Rightarrow> ('var \<times> 'annot) set"
  fixes closed :: "'preform \<Rightarrow> bool"
  assumes annotate_preserves_fv: "fst ` fv (annotate a pf) = pre_fv pf"
  assumes fv_subst: "fv (subst s f) \<subseteq> ran_fv s"
  assumes closed_eq: "closed pf \<Longrightarrow> subst s1 (annotate a1 pf) = subst s2 (annotate a2 pf)"

locale Abstract_Rules =
  Abstract_Formulas _ pre_fv _ subst
  for pre_fv :: "'preform \<Rightarrow> 'var set" and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" +
  fixes antecedent :: "'rule \<Rightarrow> ('preform list \<times> 'preform) list"
  fixes consequent :: "'rule \<Rightarrow> 'preform list"
  and rules :: "'rule stream"
begin
  definition f_antecedent :: "'rule \<Rightarrow> ('preform fset \<times> 'preform) fset"
    where "f_antecedent r = (fset_from_list (map (apfst fset_from_list) (antecedent r)))"
  definition "f_consequent r = (fset_from_list (consequent r))"

end

locale Abstract_Task =
  Abstract_Rules  _ _ _ _ pre_fv _ _ _ rules
  for rules :: "'rule stream" and pre_fv :: "'preform \<Rightarrow> 'var set" + 
  fixes assumptions :: "'preform list"
  fixes conclusions :: "'preform list"
  assumes assumptions_closed: "\<forall>a \<in> set assumptions. closed a"
  assumes conclusions_closed: "\<forall>c \<in> set conclusions. closed a"
  assumes no_empty_conclusions: "\<forall>xs\<in>sset rules. consequent xs \<noteq> []"
begin
  definition ass_forms where "ass_forms = fset_from_list (map (subst undefined) (map (annotate undefined) assumptions))"
  definition conc_forms where "conc_forms = fset_from_list (map (subst undefined) (map (annotate undefined) conclusions))"

  lemma subst_annotate_in_ass_formsI:
    assumes "pf \<in> set assumptions"
    shows "subst s (annotate a pf) |\<in>| ass_forms"
      using assms ass_forms_def assumptions_closed closed_eq by fastforce

  lemma subst_annotate_in_conc_formsI:
    assumes "pf \<in> set conclusions"
    shows "subst s (annotate a pf) |\<in>| conc_forms"
      using assms conc_forms_def conclusions_closed closed_eq by fastforce
end

end