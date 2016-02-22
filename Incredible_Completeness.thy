theory Incredible_Completeness
imports Natural_Deduction Incredible_Deduction
begin

lemma image_eq_to_f:
  assumes  "f1 ` S1 = f2 ` S2"
  obtains f where "\<And> x. x \<in> S2 \<Longrightarrow> f x \<in> S1 \<and> f1 (f x) = f2 x"
proof (atomize_elim)
  from assms
  have "\<forall>x. x \<in> S2 \<longrightarrow> (\<exists> y. y \<in> S1 \<and> f1 y = f2 x)" by (metis image_iff)
  thus "\<exists>f. \<forall>x. x \<in> S2 \<longrightarrow> f x \<in> S1 \<and> f1 (f x) = f2 x" by metis
qed

context includes fset.lifting
begin
lemma fimage_eq_to_f:
  assumes  "f1 |`| S1 = f2 |`| S2"
  obtains f where "\<And> x. x |\<in>| S2 \<Longrightarrow> f x |\<in>| S1 \<and> f1 (f x) = f2 x"
using assms apply transfer using image_eq_to_f by metis
end


section {* Elaborated tree (annotation and substitution) *}

text {*
Tree-shape, but incredible-graph-like content (port names, explicit annotation and substitution)
*}

datatype ('preform,'rule,'subst,'var)  itree =
    INode (iNodeOf: "('preform, 'rule) graph_node")
          (iOutPort: "'preform reg_out_port")
          (iAnnot: "nat")
          (iSubst: "'subst")
          (iAnts: "('preform, 'var) in_port \<rightharpoonup> ('preform,'rule,'subst,'var) itree")

context Abstract_Task
begin
  inductive iwf :: "('preform,'rule,'subst,'var) itree \<Rightarrow> 'form entailment \<Rightarrow> bool" where
    iwf: "\<lbrakk>
       Reg p |\<in>| outPorts n;
       \<And> ip. ip |\<in>| inPorts n \<Longrightarrow>
          subst s (freshen i (labelsIn n ip)) |\<notin>| ass_forms \<and>
          subst s (freshen i (labelsIn n ip)) |\<in>| (\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<or>
          (\<exists> t. ants ip = Some t \<and>
              iwf t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))));
       \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenV i ` (local_vars n ip) \<inter> fv f = {};
       \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> freshenV i ` (local_vars n ip) \<inter> ran_fv s = {};
       c = subst s (freshen i (labelsOut n (Reg p :: (('preform, 'var) out_port))))
      \<rbrakk> \<Longrightarrow> iwf (INode n p i s ants) (\<Gamma> \<turnstile> c)"  

fun del_global_assn :: "'form entailment \<Rightarrow> 'form entailment" where
  "del_global_assn (\<Gamma> \<turnstile> c) = (\<Gamma> |-| ass_forms \<turnstile> c)"


lemma build_iwf:
  fixes t :: "('form entailment \<times> ('rule \<times> 'preform) NatRule) tree"
  assumes "tfinite t"
  assumes "wf t"
  shows "\<exists> it. iwf it (fst (root t))"
using assms
proof(induction)
  case (tfinite t)
  from `wf t`
  have "snd (root t) \<in> R" using wf.simps by blast

  from `wf t`
  have "eff (snd (root t)) (fst (root t)) ((fst \<circ> root) |`| cont t)" using wf.simps by blast

  from `wf t`
  have "\<And> t'. t' |\<in>| cont t \<Longrightarrow> wf t'" using wf.simps by blast
  hence IH: "\<And> \<Gamma>' t'. t' |\<in>| cont t \<Longrightarrow> (\<exists>it'. iwf it' (fst (root t')))" using tfinite(2) by blast
  then obtain its where its: "\<And> t'. t' |\<in>| cont t \<Longrightarrow> iwf (its t') (fst (root t'))"
    by metis

  from `eff _ _ _`
  show ?case
  proof(cases rule: eff.cases[case_names Axiom NatRule Cut])
  case (Axiom con \<Gamma>)
    show ?thesis
    proof (cases "con |\<in>| ass_forms")
      case True (* Global assumption *)
      then obtain c :: "'preform" where
        "c \<in> set assumptions" and [simp]: "subst undefined (freshen undefined c) = con"
        by (auto simp add:  ass_forms_def)

      let "?it" = "INode (Assumption c) c undefined undefined empty ::  ('preform, 'rule, 'subst, 'var) itree"

      have "iwf ?it (\<Gamma> \<turnstile> con)"  by (auto intro: iwf)
      thus ?thesis unfolding Axiom..
    next
      case False
      obtain s where [simp]: "subst s (freshen undefined anyP) = con" by atomize_elim (rule anyP_is_any)
  
      let "?it" = "INode Helper anyP undefined s empty ::  ('preform, 'rule, 'subst, 'var) itree"
  
      from  `con |\<in>| \<Gamma>` False
      have "iwf ?it (\<Gamma> \<turnstile> con)" by (auto intro: iwf)
      thus ?thesis unfolding Axiom..
    qed
  next
  case (NatRule r c ants \<Gamma> i s rule)
    from `natEff_Inst r c ants`
    have "snd r = c"  and [simp]: "f_antecedent (fst r) = ants" and "c \<in> set (consequent (fst r))"
      by (auto simp add: natEff_Inst.simps)  

    from `(fst \<circ> root) |\`| cont t = (\<lambda>ant. (\<lambda>p. subst s (freshen i p)) |\`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant))) |\`| ants`
    obtain to_t where "\<And> ant. ant |\<in>| ants \<Longrightarrow> to_t ant |\<in>| cont t \<and> (fst \<circ> root) (to_t ant) = ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
      by (rule fimage_eq_to_f) (rule that)
    hence to_t_in_cont: "\<And> ant. ant |\<in>| ants \<Longrightarrow> to_t ant |\<in>| cont t"
      and to_t_root: "\<And> ant. ant |\<in>| ants \<Longrightarrow>  fst (root (to_t ant)) = ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
      by auto

    let "?it" = "INode (Rule (fst r)) c i s (\<lambda> ant. if ant |\<in>| ants then Some (its (to_t ant)) else None) ::  ('preform, 'rule, 'subst, 'var) itree"

    from `c \<in> set (consequent (fst r))`
    have "c |\<in>| f_consequent (fst r)" by (simp add: f_consequent_def)
    moreover
    { fix ant
      assume "ant |\<in>| ants"
      from its[OF to_t_in_cont[OF this]]
      have "iwf (its (to_t ant)) (fst (root (to_t ant)))".
      also have "fst (root (to_t ant)) =
        ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst r)) h))) |`| hyps_for (Rule (fst r)) ant |\<union>| \<Gamma>
         \<turnstile> subst s (freshen i (a_conc ant)))"
        by (auto simp add: to_t_root `ant |\<in>| ants`)
      finally
      have "iwf (its (to_t ant))
           ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst r)) h))) |`| hyps_for (Rule (fst r)) ant |\<union>|
            \<Gamma>  \<turnstile> subst s (freshen i (a_conc ant)))".
    }
    moreover
    note NatRule(5,6)
    ultimately
    have "iwf ?it ((\<Gamma> \<turnstile> subst s (freshen i c)))"
      apply -
      apply (rule iwf)
      apply auto
      apply blast
      done
    thus ?thesis unfolding NatRule..
  next
  case (Cut \<Gamma> con)
    obtain s where [simp]: "subst s (freshen undefined anyP) = con" by atomize_elim (rule anyP_is_any)

    from `(fst \<circ> root) |\`| cont t = {|\<Gamma> \<turnstile> con|}`
    obtain t'  where "t' |\<in>| cont t" and [simp]: "fst (root t') = (\<Gamma> \<turnstile> con)"
      by (cases "cont t") auto
    
    from `t' |\<in>| cont t` obtain "it'" where "iwf it' (\<Gamma> \<turnstile> con)" using IH by force

    let "?it" = "INode Helper anyP undefined s (empty(plain_ant anyP \<mapsto> it')) ::  ('preform, 'rule, 'subst, 'var) itree"

    from `iwf it' (\<Gamma> \<turnstile> con)`
    have "iwf ?it (\<Gamma> \<turnstile> con)"
      by (auto intro: iwf)
    thus ?thesis unfolding Cut..
  qed 
qed

definition to_it :: "('form entailment \<times> ('rule \<times> 'preform) NatRule) tree \<Rightarrow> ('preform,'rule,'subst,'var) itree" where
  "to_it t = (SOME it. iwf it (fst (root t)))"

lemma iwf_to_it:
  assumes "tfinite t" and "wf t"
  shows "iwf (to_it t) (fst (root t))"
unfolding to_it_def using build_iwf[OF assms] by (rule someI2_ex)


  fun fv_entailment :: "'form entailment \<Rightarrow> 'var annotated set" where
    "fv_entailment (\<Gamma> \<turnstile> c) = Union (fv ` fset \<Gamma>) \<union> fv c"

  inductive iwf' :: "('preform,'rule,'subst,'var) itree \<Rightarrow> 'form entailment \<Rightarrow> bool" where
    iwf': "\<lbrakk>
       Reg p |\<in>| outPorts n;
       \<And> ip. ip |\<in>| inPorts n \<Longrightarrow>
          subst s (freshen i (labelsIn n ip)) |\<notin>| ass_forms \<and>
          subst s (freshen i (labelsIn n ip)) |\<in>| (\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<or>
          (\<exists> t. ants ip = Some t \<and>
              iwf' t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))));
       ran_fv s \<subseteq> fv_entailment (\<Gamma> \<turnstile> c) \<union> range (freshenV i);
       c = subst s (freshen i (labelsOut n (Reg p :: (('preform, 'var) out_port))))
      \<rbrakk> \<Longrightarrow> iwf' (INode n p i s ants) (\<Gamma> \<turnstile> c)"  

lemma iwf'_to_it:
  assumes "tfinite t" and "wf t"
  shows "iwf' (to_it t) (fst (root t))"
sorry


inductive it_pathsP :: "('preform,'rule,'subst,'var) itree \<Rightarrow> ('preform, 'var) in_port list \<Rightarrow> bool"  where
   it_paths_Nil: "it_pathsP t []"
 | it_paths_Cons: "i |\<in>| inPorts (iNodeOf t) \<Longrightarrow> iAnts t i = Some t' \<Longrightarrow> it_pathsP t' is \<Longrightarrow> it_pathsP t (i#is)"

definition it_paths:: "('preform,'rule,'subst,'var) itree \<Rightarrow> ('preform, 'var) in_port list set"  where
  "it_paths t = Collect (it_pathsP t)"

 lemma it_paths_eq [pred_set_conv]: "it_pathsP t = (\<lambda>x. x \<in> it_paths t)"
   by(simp add: it_paths_def)

 lemmas it_paths_intros [intro?] = it_pathsP.intros[to_set]
 lemmas it_paths_induct [consumes 1, induct set: it_paths] = it_pathsP.induct[to_set]
 lemmas it_paths_cases [consumes 1, cases set: it_paths] = it_pathsP.cases[to_set]
 lemmas it_paths_simps = it_pathsP.simps[to_set]


lemma it_paths_Union: "it_paths t \<subseteq> insert [] (Union (fset ((\<lambda> i. case iAnts t i of Some t \<Rightarrow> (op # i) ` it_paths t | None \<Rightarrow> {}) |`| (inPorts (iNodeOf t)))))"
  apply (rule)
  apply (subst (asm) it_paths_simps)
  apply (fastforce split: prod.split simp add: fmember.rep_eq)
  done

lemma finite_it_paths[simp]: "finite (it_paths t)"
  apply (induction t)
  apply (rule finite_subset[OF it_paths_Union])
  apply (fastforce split: option.split intro: range_eqI)
  done

end

fun tree_at :: "('preform,'rule,'subst,'var) itree \<Rightarrow> ('preform, 'var) in_port list \<Rightarrow> ('preform,'rule,'subst,'var) itree" where
  "tree_at t [] = t"
| "tree_at t (i#is) = tree_at (the (iAnts t i)) is"

type_synonym ('preform, 'var) vertex = "('preform \<times> ('preform, 'var) in_port list option)"

locale Solved_Task =
  Abstract_Task freshen pre_fv fv subst ran_fv closed anyP antecedent consequent rules assumptions conclusions
  for   ran_fv :: "'subst \<Rightarrow> ('var \<times> nat) set" 
    and closed :: "'preform \<Rightarrow> bool" 
    and anyP :: "'preform" 
    and freshen :: "nat \<Rightarrow> 'preform \<Rightarrow> 'form" 
    and pre_fv :: "'preform \<Rightarrow> 'var set" 
    and fv :: "'form \<Rightarrow> ('var \<times> nat) set" 
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent list" 
    and consequent :: "'rule \<Rightarrow> 'preform list" 
    and rules :: "'rule stream" 
    and assumptions :: "'preform list" 
    and conclusions :: "'preform list" +
  assumes solved: solved
begin

text {* Lets get our hand on concrete trees *}

definition ts :: "'form \<Rightarrow> (('form entailment) \<times> ('rule \<times> 'preform) NatRule) tree" where
  "ts c = (SOME t. snd (fst (root t)) = c \<and> fst (fst (root t)) |\<subseteq>| ass_forms \<and> wf t \<and> tfinite t)"

lemma
  assumes "c |\<in>| conc_forms"
  shows ts_conc: "snd (fst (root (ts c))) = c"
  and   ts_context: "fst (fst (root (ts c))) |\<subseteq>| ass_forms"
  and   ts_wf: "wf (ts c)"
  and   ts_finite[simp]: "tfinite (ts c)"
  unfolding atomize_conj conj_assoc ts_def
  apply (rule someI_ex)
  using solved assms
  by (force simp add: solved_def)

abbreviation to_form :: "'preform \<Rightarrow> 'form" where
  "to_form pf \<equiv> subst undefined (freshen undefined pf)"
  

definition vertices :: "('preform, 'var) vertex fset"  where
  "vertices = Abs_fset (Union ( set (map (\<lambda> c. insert (c, None) ((\<lambda> p. (c, Some p)) ` (it_paths (to_it (ts (to_form c))))))  conclusions)))"

lemma mem_vertices: "v |\<in>| vertices \<longleftrightarrow>  (fst v \<in> set conclusions \<and> (snd v = None \<or> snd v \<in> Some ` it_paths (to_it (ts (to_form (fst v))))))"
  unfolding vertices_def fmember.rep_eq ffUnion.rep_eq 
  by (cases v) (auto simp add: Abs_fset_inverse Bex_def)

definition preform_of_closed_form :: "'form \<Rightarrow> 'preform" where
  "preform_of_closed_form f = (SOME pf. subst undefined (freshen undefined pf) = f)"

fun nodeOf :: "('preform, 'var) vertex \<Rightarrow> ('preform, 'rule) graph_node" where
  "nodeOf (pf, None) = Conclusion pf"
| "nodeOf (pf, Some p) = iNodeOf (tree_at (to_it (ts (to_form pf))) p)"

sublocale Tasked_Proof_Graph freshen fv ran_fv closed anyP subst pre_fv antecedent consequent fresh_vars rules assumptions conclusions
  vertices nodeOf
  sorry

end
