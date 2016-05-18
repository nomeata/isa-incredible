theory Build_Incredible_Tree
imports Incredible_Trees Natural_Deduction
begin

context  Abstract_Task
begin

lemma build_local_iwf:
  fixes t :: "('form entailment \<times> ('rule \<times> 'form) NatRule) tree"
  assumes "tfinite t"
  assumes "wf t"
  shows "\<exists> it. local_iwf it (fst (root t))"
using assms
proof(induction)
  case (tfinite t)
  from `wf t`
  have "snd (root t) \<in> R" using wf.simps by blast

  from `wf t`
  have "eff (snd (root t)) (fst (root t)) ((fst \<circ> root) |`| cont t)" using wf.simps by blast

  from `wf t`
  have "\<And> t'. t' |\<in>| cont t \<Longrightarrow> wf t'" using wf.simps by blast
  hence IH: "\<And> \<Gamma>' t'. t' |\<in>| cont t \<Longrightarrow> (\<exists>it'. local_iwf it' (fst (root t')))" using tfinite(2) by blast
  then obtain its where its: "\<And> t'. t' |\<in>| cont t \<Longrightarrow> local_iwf (its t') (fst (root t'))" by metis

  from `eff _ _ _`
  show ?case               
  proof(cases rule: eff.cases[case_names Axiom NatRule Cut])
  case (Axiom c \<Gamma>)
    show ?thesis
    proof (cases "c |\<in>| ass_forms")
      case True (* Global assumption *)
      then  have "c \<in> set assumptions"  by (auto simp add:  ass_forms_def)

      let "?it" = "INode (Assumption c) c undefined undefined [] ::  ('form, 'rule, 'subst, 'var) itree"

      from `c \<in> set assumptions`
      have "local_iwf ?it (\<Gamma> \<turnstile> c)"
        by (auto intro!: iwf local_fresh_check.intros)

      thus ?thesis unfolding Axiom..
    next
      case False
      obtain s where "subst s anyP = c" by atomize_elim (rule anyP_is_any)
      hence [simp]: "subst s (freshen undefined anyP) = c" by (simp add: lconsts_anyP freshen_closed)
  
      let "?it" = "HNode undefined s ::  ('form, 'rule, 'subst, 'var) itree"
  
      from  `c |\<in>| \<Gamma>` False
      have "local_iwf ?it (\<Gamma> \<turnstile> c)" by (auto intro: iwfH)
      thus ?thesis unfolding Axiom..
    qed
  next
  case (NatRule rule c ants \<Gamma> i s)
    from `natEff_Inst rule c ants`
    have "snd rule = c"  and [simp]: "ants = f_antecedent (fst rule)" and "c \<in> set (consequent (fst rule))"
      by (auto simp add: natEff_Inst.simps)  

    from `(fst \<circ> root) |\`| cont t = (\<lambda>ant. (\<lambda>p. subst s (freshen i p)) |\`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant))) |\`| ants`
    obtain to_t where "\<And> ant. ant |\<in>| ants \<Longrightarrow> to_t ant |\<in>| cont t \<and> (fst \<circ> root) (to_t ant) = ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
      by (rule fimage_eq_to_f) (rule that)
    hence to_t_in_cont: "\<And> ant. ant |\<in>| ants \<Longrightarrow> to_t ant |\<in>| cont t"
      and to_t_root: "\<And> ant. ant |\<in>| ants \<Longrightarrow>  fst (root (to_t ant)) = ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
      by auto

    let ?ants' = "map (\<lambda> ant. its (to_t ant)) (antecedent (fst rule))"
    let "?it" = "INode (Rule (fst rule)) c i s ?ants' ::  ('form, 'rule, 'subst, 'var) itree"

    from `snd (root t) \<in> R`
    have "fst rule \<in> sset rules"
      unfolding NatRule
      by (auto simp add: stream.set_map n_rules_def no_empty_conclusions )
    moreover
    from `c \<in> set (consequent (fst rule))`
    have "c |\<in>| f_consequent (fst rule)" by (simp add: f_consequent_def)
    moreover
    { fix ant
      assume "ant \<in> set (antecedent (fst rule))"
      hence "ant |\<in>| ants" by (simp add: f_antecedent_def)
      from its[OF to_t_in_cont[OF this]]
      have "local_iwf (its (to_t ant)) (fst (root (to_t ant)))".
      also have "fst (root (to_t ant)) =
        ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
        by (rule to_t_root[OF `ant |\<in>| ants`])
      also have "\<dots> =
        ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst rule)) h))) |`| hyps_for (Rule (fst rule)) ant |\<union>| \<Gamma>
         \<turnstile> subst s (freshen i (a_conc ant)))" 
         using \<open>ant |\<in>| ants\<close>
         by auto
      finally
      have "local_iwf (its (to_t ant))
           ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst rule)) h))) |`| hyps_for (Rule (fst rule)) ant |\<union>|
            \<Gamma>  \<turnstile> subst s (freshen i (a_conc ant)))".
    }
    moreover
    from NatRule(5,6)
    have "local_fresh_check (Rule (fst rule)) i s (\<Gamma> \<turnstile> subst s (freshen i c))"
      by (fastforce intro!: local_fresh_check.intros simp add: all_local_vars_def fmember.rep_eq)
    ultimately
    have "local_iwf ?it ((\<Gamma> \<turnstile> subst s (freshen i c)))"
      by (intro iwf ) (auto simp add: list_all2_map2 list_all2_same)
    thus ?thesis unfolding NatRule..
  next
  case (Cut \<Gamma> con)
    obtain s where "subst s anyP = con" by atomize_elim (rule anyP_is_any)
    hence  [simp]: "subst s (freshen undefined anyP) = con" by (simp add: lconsts_anyP freshen_closed)

    from `(fst \<circ> root) |\`| cont t = {|\<Gamma> \<turnstile> con|}`
    obtain t'  where "t' |\<in>| cont t" and [simp]: "fst (root t') = (\<Gamma> \<turnstile> con)"
      by (cases "cont t") auto
    
    from `t' |\<in>| cont t` obtain "it'" where "local_iwf it' (\<Gamma> \<turnstile> con)" using IH by force

    let "?it" = "INode Helper anyP undefined s [it'] ::  ('form, 'rule, 'subst, 'var) itree"

    from `local_iwf it' (\<Gamma> \<turnstile> con)`
    have "local_iwf ?it (\<Gamma> \<turnstile> con)" by (auto intro!: iwf local_fresh_check.intros)
    thus ?thesis unfolding Cut..
  qed 
qed

definition to_it :: "('form entailment \<times> ('rule \<times> 'form) NatRule) tree \<Rightarrow> ('form,'rule,'subst,'var) itree" where
  "to_it t = (SOME it. local_iwf it (fst (root t)))"

lemma iwf_to_it:
  assumes "tfinite t" and "wf t"
  shows "local_iwf (to_it t) (fst (root t))"
unfolding to_it_def using build_local_iwf[OF assms] by (rule someI2_ex)

end

end