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
end


locale Abstract_Formulas =
  fixes annotate :: "'annot \<Rightarrow> 'preform \<Rightarrow> 'form"
  fixes pre_fv :: "'preform \<Rightarrow> 'var set"
  fixes fv :: "'form \<Rightarrow> ('var \<times> 'annot) set"
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  fixes ran_fv :: "'subst \<Rightarrow> ('var \<times> 'annot) set"
  assumes annotate_preserves_fv: "fst ` fv (annotate a pf) = pre_fv pf"
  assumes fv_subst: "fv (subst s f) \<subseteq> ran_fv s"

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
  Abstract_Rules  _ _ _ pre_fv _ _ _ rules
  for rules :: "'rule stream" and pre_fv :: "'preform \<Rightarrow> 'var set" + 
  fixes assumptions :: "'preform list"
  fixes conclusions :: "'preform list"
  assumes no_empty_conclusions: "\<forall>xs\<in>sset rules. consequent xs \<noteq> []"


end