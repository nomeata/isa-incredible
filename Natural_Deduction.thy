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

locale ND_Rules = 
  fixes natEff :: "'rule \<Rightarrow> 'form \<Rightarrow> 'form entailment fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  fun eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
     "eff Axiom (ctxt \<turnstile> con) ant \<longleftrightarrow> ant = {||} \<and> con |\<in>| ctxt"
   | "eff (NatRule rule) (ctxt \<turnstile> con) ant \<longleftrightarrow> (\<exists> nat_ant. natEff rule con nat_ant \<and> ant = fimage (\<lambda> n . (fst n |\<union>| ctxt, snd n) ) nat_ant)"
  
  sublocale RuleSystem_Defs where
    eff = eff and rules = "Axiom ## smap NatRule rules".

  lemma effNatRuleI:
    "natEff rule con nat_ant \<Longrightarrow> eff (NatRule rule) (ctxt, con) (fimage (\<lambda> n . (fst n |\<union>| ctxt, snd n) ) nat_ant)"
      by auto

end

locale ND_Rules_Inst =
  Abstract_Formulas _ pre_fv _ subst
  for pre_fv :: "'preform \<Rightarrow> 'var set" and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" +
  fixes natEff_Inst :: "'rule \<Rightarrow> 'preform \<Rightarrow> ('preform, 'var) antecedent fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  inductive natEff where
    "natEff_Inst r c ants \<Longrightarrow> 
     natEff r (subst s (annotate a c)) ((\<lambda>ant. ((\<lambda>p. subst s (annotate a p)) |`| a_hyps ant \<turnstile> subst s (annotate a (a_concl ant)))) |`| ants)"

  sublocale ND_Rules where natEff = natEff and rules = rules.
end

context Abstract_Task 
begin           
  inductive natEff_Inst where
    "c \<in> set (consequent r) \<Longrightarrow> natEff_Inst (r,c) c (f_antecedent r)"

  definition n_rules where
    "n_rules = flat (smap (\<lambda>r. map (\<lambda>c. (r,c)) (consequent r)) rules)"
  
  sublocale ND_Rules_Inst _ _ _ _ _ _ natEff_Inst n_rules ..

  definition solved where
    "solved \<longleftrightarrow> (\<forall> c. c |\<in>| conc_forms \<longrightarrow> (\<exists> t. fst (root t) = (ass_forms, c) \<and> wf t \<and> tfinite t))"
    
end


end