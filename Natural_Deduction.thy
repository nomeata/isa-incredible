theory Natural_Deduction
imports
  Main
  "$AFP/Abstract_Completeness/Abstract_Completeness"
  Abstract_Formula
begin

datatype 'rule NatRule = Axiom | NatRule 'rule

type_synonym 'form entailment = "('form fset \<times> 'form)"

abbreviation entails :: "'form fset \<Rightarrow> 'form \<Rightarrow> 'form entailment" (infix "\<turnstile>" 50)
  where "entails a c \<equiv> (a, c)"

fun add_ctxt :: "'form fset \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment" where
  "add_ctxt \<Delta> (\<Gamma> \<turnstile> c) = (\<Gamma> |\<union>| \<Delta> \<turnstile> c)"

locale ND_Rules_Simple = 
  fixes natEff :: "'rule \<Rightarrow> 'form \<Rightarrow> 'form entailment fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  inductive eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
    "con |\<in>| \<Gamma> \<Longrightarrow> eff Axiom (\<Gamma> \<turnstile> con) {||}"
   |"natEff rule con ant \<Longrightarrow> eff (NatRule rule) (\<Gamma> \<turnstile> con) (add_ctxt \<Gamma> |`| ant)"
  
  sublocale RuleSystem_Defs where
    eff = eff and rules = "Axiom ## smap NatRule rules".
end

locale ND_Rules_Inst =
  Abstract_Formulas freshen pre_fv fv subst ran_fv closed
  for freshen :: "'annot \<Rightarrow> 'preform \<Rightarrow> 'form" 
  and pre_fv :: "'preform \<Rightarrow> 'var set" 
  and fv :: "'form \<Rightarrow> ('var \<times> 'annot) set" 
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and ran_fv :: "'subst \<Rightarrow> ('var \<times> 'annot) set" 
  and closed :: "'preform \<Rightarrow> bool" +

  fixes nat_rule :: "'rule \<Rightarrow> 'preform \<Rightarrow> ('preform, 'var) antecedent fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  inductive eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
    "con |\<in>| \<Gamma>
    \<Longrightarrow> eff Axiom (\<Gamma> \<turnstile> con) {||}"
   |"nat_rule r c ants
    \<Longrightarrow> (\<And> ant f. ant |\<in>| ants \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenV a ` (a_fresh ant) \<inter> fv f = {})
    \<Longrightarrow> (\<And> ant. ant |\<in>| ants \<Longrightarrow> freshenV a ` (a_fresh ant) \<inter> ran_fv s = {})
    \<Longrightarrow> eff (NatRule rule)
        (\<Gamma> \<turnstile> subst s (freshen a c))
        ((\<lambda>ant. ((\<lambda>p. subst s (annotate a p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (annotate a (a_conc ant)))) |`| ants) "
    
(*
     natEff r (subst s (freshen a c))
              ((\<lambda>ant. ((\<lambda>p. subst s (annotate a p)) |`| a_hyps ant \<turnstile> subst s (annotate a (a_conc ant)))) |`| ants)"
*)
  sublocale RuleSystem_Defs where
    eff = eff and rules = "Axiom ## smap NatRule rules".
end

context Abstract_Task 
begin           
  inductive natEff_Inst where
    "c \<in> set (consequent r) \<Longrightarrow> natEff_Inst (r,c) c (f_antecedent r)"

  definition n_rules where
    "n_rules = flat (smap (\<lambda>r. map (\<lambda>c. (r,c)) (consequent r)) rules)"
  
  sublocale ND_Rules_Inst _ _ _ _ _ _ natEff_Inst n_rules ..

  definition solved where
    "solved \<longleftrightarrow> (\<forall> c. c |\<in>| conc_forms \<longrightarrow> (\<exists> \<Gamma> t. fst (root t) = (\<Gamma> \<turnstile> c) \<and> \<Gamma> |\<subseteq>| ass_forms \<and> wf t \<and> tfinite t))"

end


end