theory Natural_Deduction
imports
  Main
  "$AFP/Abstract_Completeness/Abstract_Completeness"
  Abstract_Formula
begin

datatype 'rule NatRule = Axiom | NatRule 'rule | Cut

type_synonym 'form entailment = "('form fset \<times> 'form)"

abbreviation entails :: "'form fset \<Rightarrow> 'form \<Rightarrow> 'form entailment" (infix "\<turnstile>" 50)
  where "a \<turnstile> c \<equiv> (a, c)"

fun add_ctxt :: "'form fset \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment" where
  "add_ctxt \<Delta> (\<Gamma> \<turnstile> c) = (\<Gamma> |\<union>| \<Delta> \<turnstile> c)"

locale ND_Rules_Simple = 
  fixes natEff :: "'rule \<Rightarrow> 'form \<Rightarrow> 'form entailment fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  inductive eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
    eff_Axiom:
    "con |\<in>| \<Gamma> \<Longrightarrow> eff Axiom (\<Gamma> \<turnstile> con) {||}"
   |eff_Rule:
    "natEff rule con ant \<Longrightarrow> eff (NatRule rule) (\<Gamma> \<turnstile> con) (add_ctxt \<Gamma> |`| ant)"
   |eff_Cut:
    "eff Cut (\<Gamma> \<turnstile> con) {| \<Gamma> \<turnstile> con |}"

  
  sublocale RuleSystem_Defs where
    eff = eff and rules = "Cut ## Axiom ## smap NatRule rules".
end

locale ND_Rules_Inst =
  Abstract_Formulas freshen pre_fv fv subst ran_fv closed
  for freshen :: "nat \<Rightarrow> 'preform \<Rightarrow> 'form" 
  and pre_fv :: "'preform \<Rightarrow> 'var set" 
  and fv :: "'form \<Rightarrow> 'var annotated set" 
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and ran_fv :: "'subst \<Rightarrow> 'var annotated set" 
  and closed :: "'preform \<Rightarrow> bool" +

  fixes nat_rule :: "'rule \<Rightarrow> 'preform \<Rightarrow> ('preform, 'var) antecedent fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  inductive eff :: "'rule NatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
    "con |\<in>| \<Gamma>
    \<Longrightarrow> eff Axiom (\<Gamma> \<turnstile> con) {||}"
   |"nat_rule rule c ants
    \<Longrightarrow> (\<And> ant f. ant |\<in>| ants \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenV a ` (a_fresh ant) \<inter> fv f = {})
    \<Longrightarrow> (\<And> ant. ant |\<in>| ants \<Longrightarrow> freshenV a ` (a_fresh ant) \<inter> ran_fv s = {})
    \<Longrightarrow> eff (NatRule rule)
        (\<Gamma> \<turnstile> subst s (freshen a c))
        ((\<lambda>ant. ((\<lambda>p. subst s (freshen a p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen a (a_conc ant)))) |`| ants) "
   |"eff Cut (\<Gamma> \<turnstile> c') {| (\<Gamma> \<turnstile> c')|}"

 inductive_simps eff_Cut_simps[simp]: "eff Cut (\<Gamma> \<turnstile> c) S"

(*
     natEff r (subst s (freshen a c))
              ((\<lambda>ant. ((\<lambda>p. subst s (annotate a p)) |`| a_hyps ant \<turnstile> subst s (annotate a (a_conc ant)))) |`| ants)"
*)
  sublocale RuleSystem_Defs where
    eff = eff and rules = "Cut ## Axiom ## smap NatRule rules".
end

context Abstract_Task 
begin           
  inductive natEff_Inst where
    "c \<in> set (consequent r) \<Longrightarrow> natEff_Inst (r,c) c (f_antecedent r)"

  definition n_rules where
    "n_rules = flat (smap (\<lambda>r. map (\<lambda>c. (r,c)) (consequent r)) rules)"
  
  sublocale ND_Rules_Inst _ _ _ _ _ _ _ natEff_Inst n_rules ..

  definition solved where
    "solved \<longleftrightarrow> (\<forall> c. c |\<in>| conc_forms \<longrightarrow> (\<exists> \<Gamma> t. fst (root t) = (\<Gamma> \<turnstile> c) \<and> \<Gamma> |\<subseteq>| ass_forms \<and> wf t \<and> tfinite t))"


end

(*

section {* Elaborated tree (annotation and substitution) *}

datatype ('rule, 'annot, 'subst) ElaboratedNatRule = EAxiom | ENatRule 'rule 'annot 'subst

fun deElaborate where
  "deElaborate EAxiom = Axiom"
 |"deElaborate (ENatRule r a s) = NatRule r"

context ND_Rules_Inst
begin

  inductive eeff :: "('rule,'annot,'subst) ElaboratedNatRule \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment fset \<Rightarrow> bool" where
   eeff_EAxiom:
   "con |\<in>| \<Gamma>
    \<Longrightarrow> eeff EAxiom (\<Gamma> \<turnstile> con) {||}"
   | eeff_ERule:
   "nat_rule r c ants
    \<Longrightarrow> (\<And> ant f. ant |\<in>| ants \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenV a ` (a_fresh ant) \<inter> fv f = {})
    \<Longrightarrow> (\<And> ant. ant |\<in>| ants \<Longrightarrow> freshenV a ` (a_fresh ant) \<inter> ran_fv s = {})
    \<Longrightarrow> eeff (ENatRule rule a s)
        (\<Gamma> \<turnstile> subst s (freshen a c))
        ((\<lambda>ant. ((\<lambda>p. subst s (freshen a p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen a (a_conc ant)))) |`| ants) "

  coinductive ewf :: "('form entailment \<times> ('rule, 'annot, 'subst) ElaboratedNatRule) tree \<Rightarrow> bool" where
    ewf: "\<lbrakk>
        deElaborate (snd (root t)) \<in> R;
        eeff (snd (root t)) (fst (root t)) (fimage (fst o root) (cont t));
        \<And>t'. t' |\<in>| cont t \<Longrightarrow> ewf t'
      \<rbrakk> \<Longrightarrow> ewf t"

  definition elaborate_step where
    "elaborate_step r con ants = (SOME er. eeff er con ants \<and> deElaborate er = r)"

  lemma elaborate_tree_eeff:
    assumes "eff r con ants"
    shows "eeff (elaborate_step r con ants) con ants \<and> deElaborate (elaborate_step r con ants) = r"
  using assms
  proof(cases rule: eff.cases[case_names Axiom Rule])
    case (Axiom h \<Gamma>)
    hence "eeff EAxiom con ants" by (auto intro!: eeff.intros)
    moreover
    have "deElaborate EAxiom = Axiom" by simp
    ultimately
    show ?thesis
      unfolding elaborate_step_def Axiom(1)
      by (intro someI conjI)
  next
    case (Rule _ _ _ _ a s rule)
    hence "eeff (ENatRule rule a s) con ants"
      by (fastforce intro!: eeff.intros)
    moreover
    have "deElaborate (ENatRule rule a s) = NatRule rule" by simp
    ultimately
    show ?thesis
      unfolding elaborate_step_def Rule(1)
      by (intro someI conjI)
  qed

  primcorec elaborate_tree where
    "root (elaborate_tree t) = (fst (root t), elaborate_step (snd (root t)) (fst (root t))  (fimage (fst o root) (cont t)))"
   |"cont (elaborate_tree t) = fimage elaborate_tree (cont t)"

  lemma fst_root_elaborate_tree[simp]:
    "fst \<circ> root \<circ> elaborate_tree = fst \<circ> root"
    by auto

  lemma elaborate_tree_deElaborate:
    assumes "wf t"
    shows "map_tree (apsnd deElaborate) (elaborate_tree t) = t"
  using assms
  proof(coinduction arbitrary: t)
  case (Eq_tree t)
    let ?er = "elaborate_step (snd (root t)) (fst (root t)) (fimage (fst o root) (cont t))"

    from Eq_tree
    have "eff (snd (root t)) (fst (root t)) (fimage (fst o root) (cont t))"
      using RuleSystem_Defs.wf.simps by blast
    from elaborate_tree_eeff[OF this]
    have "eeff ?er (fst (root t))  (fimage (fst o root) (cont t))" and "deElaborate ?er = snd (root t)" by auto
    from this(2)
    have "root (map_tree (apsnd deElaborate) (elaborate_tree t)) = root t"
      by (simp add: tree.map_sel)
    moreover
    from Eq_tree
    have "(\<forall>x. x |\<in>| cont t \<longrightarrow> wf x)" 
      using RuleSystem_Defs.wf.simps by blast
    ultimately
    show ?case
      by (auto simp add: tree.map_sel fset.rel_map rel_fset_def rel_set_def fmember.rep_eq)
  qed

  lemma elaborate_tree_ewf:
    assumes "wf t"
    shows "ewf (elaborate_tree t)"
  using assms
  proof(coinduction arbitrary: t)
  case (ewf t)
    let ?er = "elaborate_step (snd (root t)) (fst (root t)) (fimage (fst o root) (cont t))"

    from ewf
    have "snd (root t) \<in> sset (Axiom ## smap NatRule rules)"
      using wf.cases by blast
    moreover
    from ewf
    have "eff (snd (root t)) (fst (root t)) (fimage (fst o root) (cont t))"
      using wf.simps by blast
    from elaborate_tree_eeff[OF this]
    have "eeff ?er (fst (root t))  (fimage (fst o root) (cont t))" and "deElaborate ?er = snd (root t)" by auto
    moreover
    from ewf
    have "(\<forall>x. x |\<in>| cont t \<longrightarrow> wf x)" 
      using RuleSystem_Defs.wf.simps by blast
    ultimately
    show ?case
      by (auto simp del: stream.set)
  qed
    
end

section {* Elaborated tree (fixed annotation, only substitution) *}

type_synonym idx = "nat list"

inductive has_index :: "idx \<Rightarrow> ('rule, idx, 'subst) ElaboratedNatRule \<Rightarrow> bool" where
  "has_index idx EAxiom"
 |"has_index idx (ENatRule r idx s)"


(* Just fixes 'annot. When this is not a type parameter, this can just be ND_Rules_Inst*)
locale ND_Rules_Inst_Fixed =
  ND_Rules_Inst freshen pre_fv fv subst ran_fv closed nat_rule rules
  for freshen :: "idx \<Rightarrow> 'preform \<Rightarrow> 'form" 
  and pre_fv :: "'preform \<Rightarrow> 'var set" 
  and fv :: "'form \<Rightarrow> ('var \<times> idx) set" 
  and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
  and ran_fv :: "'subst \<Rightarrow> ('var \<times> idx) set" 
  and closed :: "'preform \<Rightarrow> bool"
  and nat_rule :: "'rule \<Rightarrow> 'preform \<Rightarrow> ('preform, 'var) antecedent fset \<Rightarrow> bool"
  and rules :: "'rule stream"
begin

  coinductive fewf :: "idx \<Rightarrow> ('form entailment \<times> ('rule, idx, 'subst) ElaboratedNatRule) tree \<Rightarrow> bool" where
    fewf: "\<lbrakk>
        deElaborate (snd (root t)) \<in> R;
        eeff (snd (root t)) (fst (root t)) (fimage (fst o root) (cont t));
        has_index idx (snd (root t));
        \<And>t'. t' |\<in>|\<^bsub>i\<^esub> cont t \<Longrightarrow> fewf (i#idx) t'
      \<rbrakk> \<Longrightarrow> fewf idx t"
end
*)

end