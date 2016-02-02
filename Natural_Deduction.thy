theory Natural_Deduction
imports
  Main
  "$AFP/Abstract_Completeness/Abstract_Completeness"
  Abstract_Formula
begin

datatype 'rule NatRule = Axiom | NatRule 'rule

type_synonym 'form entailment = "('form fset \<times> 'form)"

locale ND_Rules = 
  fixes natEff :: "'rule \<Rightarrow> 'form \<Rightarrow> ('form fset \<times> 'form) fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  fun eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
     "eff Axiom (ctxt, con) ant \<longleftrightarrow> ant = {||} \<and> con |\<in>| ctxt"
   | "eff (NatRule rule) (ctxt, con) ant \<longleftrightarrow> (\<exists> nat_ant. natEff rule con nat_ant \<and> ant = fimage (\<lambda> n . (fst n |\<union>| ctxt, snd n) ) nat_ant)"
  
  sublocale RuleSystem_Defs where
    eff = eff and rules = "Axiom ## smap NatRule rules".

  lemma effNatRuleI:
    "natEff rule con nat_ant \<Longrightarrow> eff (NatRule rule) (ctxt, con) (fimage (\<lambda> n . (fst n |\<union>| ctxt, snd n) ) nat_ant)"
      by auto

end

locale ND_Rules_Inst =
  Abstract_Formulas _ pre_fv _ subst
  for pre_fv :: "'preform \<Rightarrow> 'var set" and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" +
  fixes natEff_Inst :: "'rule \<Rightarrow> 'preform \<Rightarrow> ('preform fset \<times> 'preform) fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  inductive natEff where
    "natEff_Inst r c ant \<Longrightarrow> 
     natEff r (subst s (annotate a c)) (fimage (\<lambda> n . (fimage (\<lambda> p. subst s (annotate a p)) (fst n),  subst s (annotate a (snd n)))) ant)"
 
  sublocale ND_Rules where
    natEff = natEff and rules = rules.
end

context Abstract_Task 
begin
  inductive natEff_Inst where
    "c \<in> set (consequent r) \<Longrightarrow> natEff_Inst (r,c) c (f_antecedent r)"

  definition n_rules where
    "n_rules = flat (smap (\<lambda>r. map (\<lambda>c. (r,c)) (consequent r)) rules)"
  
  sublocale ND_Rules_Inst _ _ _ _ _ natEff_Inst n_rules ..
end


end