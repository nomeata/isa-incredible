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
          subst s (freshen i (labelsIn n ip)) |\<in>| (\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<or>
          (\<exists> t. ants ip = Some t \<and>
              iwf t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))));
       \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenV i ` (local_vars n ip) \<inter> fv f = {};
       \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> freshenV i ` (local_vars n ip) \<inter> ran_fv s = {};
       c = subst s (freshen i (labelsOut n (Reg p :: (('preform, 'var) out_port))))
      \<rbrakk> \<Longrightarrow> iwf (INode n p i s ants) (\<Gamma> \<turnstile> c)"  


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
  hence IH: "\<And> t'. t' |\<in>| cont t \<Longrightarrow> \<exists>it'. iwf it' (fst (root t'))" using tfinite(2) by blast
  then obtain its where its: "\<And> t'. t' |\<in>| cont t \<Longrightarrow> iwf (its t') (fst (root t'))"
    by metis

  from `eff _ _ _`
  show ?case
  proof(cases rule: eff.cases[case_names Axiom NatRule Cut])
  case (Axiom con \<Gamma>)
    obtain s where [simp]: "subst s (freshen undefined anyP) = con" by atomize_elim (rule anyP_is_any)

    let "?it" = "INode Helper anyP undefined s empty ::  ('preform, 'rule, 'subst, 'var) itree"

    from  `con |\<in>| \<Gamma>`
    have "iwf ?it (\<Gamma> \<turnstile> con)" by (auto intro: iwf)
    thus ?thesis unfolding Axiom..
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
      also have "fst (root (to_t ant)) = ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst r)) h))) |`| hyps_for (Rule (fst r)) ant |\<union>|
            \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
        by (auto simp add: to_t_root `ant |\<in>| ants`)
      finally
      have "iwf (its (to_t ant))
           ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst r)) h))) |`| hyps_for (Rule (fst r)) ant |\<union>|
            \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))".
    }
    moreover
    note NatRule(5,6)
    ultimately
    have "iwf ?it (\<Gamma> \<turnstile> subst s (freshen i c))"
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

end



inductive tpathsP :: "'a tree \<Rightarrow> nat list \<Rightarrow> bool"  where
   tpaths_Nil: "tpathsP t []"
 | tpaths_Cons: "t' |\<in>|\<^bsub>i\<^esub> cont t \<Longrightarrow> tpathsP t' is \<Longrightarrow> tpathsP t (i#is)"

definition tpaths:: "'a tree \<Rightarrow> nat list set"  where
  "tpaths t = Collect (tpathsP t)"

 lemma tpaths_eq [pred_set_conv]: "tpathsP t = (\<lambda>x. x \<in> tpaths t)"
   by(simp add: tpaths_def)

 lemmas tpaths_intros [intro?] = tpathsP.intros[to_set]
 lemmas tpaths_induct [consumes 1, induct set: tpaths] = tpathsP.induct[to_set]
 lemmas tpaths_cases [consumes 1, cases set: tpaths] = tpathsP.cases[to_set]
 lemmas tpaths_simps = tpathsP.simps[to_set]

lemma upd_nth_zero: "y < n \<Longrightarrow> x = [0..<n] ! y \<longleftrightarrow> x = y"
  apply (induction y arbitrary: x n)
  apply auto
  done

lemma tpaths_Union: "tpaths t = insert [] (Union (set (map (\<lambda> (i,t). (op # i) ` tpaths t) (indexed_members  (cont t)))))"
  apply (rule set_eqI)
  apply (subst tpaths_simps)
  apply (fastforce split: prod.split simp add: indexed_fmember_is_fmember set_zip)
  done

lemma finite_tpaths[simp]: "tfinite t \<Longrightarrow> finite (tpaths t)"
  apply (induction t rule: tfinite.induct)
  apply (subst tpaths_Union)
  apply (auto simp add: set_zip indexed_fmember_is_fmember)
  done

fun tree_at :: "'a tree \<Rightarrow> nat list \<Rightarrow> 'a tree" where
  "tree_at t [] = t"
| "tree_at t (i#is) = tree_at (cont t |!| i) is"

datatype Vertex
  = RuleV "(nat \<times> nat list)"
  | ConclusionV nat
  | AssumptionV "(nat \<times> nat list)"


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

definition ts where
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


fun isRule :: "'x NatRule \<Rightarrow> bool" where
  "isRule Axiom = False"
 |"isRule (NatRule _) = True"

fun fromRule :: "'x NatRule \<Rightarrow> 'x" where
  "fromRule Axiom = undefined"
 |"fromRule (NatRule r) = r"

inductive_set rule_paths for c where
  "is \<in> tpaths (ts c) \<Longrightarrow> isRule (snd (root (tree_at (ts c) is))) \<Longrightarrow> is \<in> rule_paths c"

lemma rule_paths_subset: "rule_paths c \<subseteq> tpaths (ts c)"
  by (auto simp add: rule_paths.simps)

lemma finite_rule_paths[simp]:
  "c |\<in>| conc_forms \<Longrightarrow> finite (rule_paths c)"
  by (meson finite_tpaths rev_finite_subset rule_paths_subset ts_finite)

inductive isAssumption :: "'form \<Rightarrow> 'x NatRule \<Rightarrow> bool" where
  "c |\<in>| ass_forms \<Longrightarrow> isAssumption c Axiom"

inductive_set assm_paths for c where
  "is \<in> tpaths (ts c) \<Longrightarrow> isAssumption  (snd (fst (root (tree_at (ts c) is))))  (snd (root (tree_at (ts c) is))) \<Longrightarrow> is \<in> assm_paths c"

lemma assm_paths_subset: "assm_paths c \<subseteq> tpaths (ts c)"
  by (auto simp add: assm_paths.simps)

lemma finite_assm_paths[simp]:
  "c |\<in>| conc_forms \<Longrightarrow> finite (assm_paths c)"
  by (meson finite_tpaths rev_finite_subset assm_paths_subset ts_finite)

definition rule_vertices where
  "rule_vertices = Abs_fset ((Union (set (map (\<lambda> (i,c). (Pair i) ` rule_paths c) (indexed_members conc_forms)))))"

lemma mem_rule_vertices: "v |\<in>| rule_vertices \<longleftrightarrow> (\<exists> c. c |\<in>|\<^bsub>fst v\<^esub> conc_forms \<and> snd v \<in> rule_paths c)"
  unfolding rule_vertices_def
  apply (subst fmember.abs_eq)
  apply (auto simp add: eq_onp_same_args indexed_fmember_is_fmember)[1]
  apply (cases "v")
  apply (auto simp add: Bex_def)
  done

lemma mem_rule_vertices2: "v |\<in>| rule_vertices \<longleftrightarrow> fst v < size conc_forms \<and> snd v \<in> rule_paths (conc_forms |!| fst v)"
  unfolding rule_vertices_def
  apply (cases v)
  apply (subst fmember.abs_eq)
  apply (auto simp add: eq_onp_same_args indexed_fmember_is_fmember)[1]
  apply (auto simp add: Bex_def indexed_fmember_fnth )
  done

definition assm_vertices where
  "assm_vertices = Abs_fset ((Union (set (map (\<lambda> (i,c). (Pair i) ` assm_paths c) (indexed_members conc_forms)))))"

lemma mem_assm_vertices: "v |\<in>| assm_vertices \<longleftrightarrow> (\<exists> c. c |\<in>|\<^bsub>fst v\<^esub> conc_forms \<and> snd v \<in> assm_paths c)"
  unfolding assm_vertices_def
  apply (subst fmember.abs_eq)
  apply (auto simp add: eq_onp_same_args indexed_fmember_is_fmember)[1]
  apply (cases "v")
  apply (auto simp add: Bex_def)
  done

lemma mem_assm_vertices2: "v |\<in>| assm_vertices \<longleftrightarrow> fst v < size conc_forms \<and> snd v \<in> assm_paths (conc_forms |!| fst v)"
  unfolding assm_vertices_def
  apply (cases v)
  apply (subst fmember.abs_eq)
  apply (auto simp add: eq_onp_same_args indexed_fmember_is_fmember)[1]
  apply (auto simp add: Bex_def indexed_fmember_fnth )
  done

definition conc_vertices where
  "conc_vertices = fidx conc_forms |`| conc_forms"

definition vertices where
  "vertices = RuleV |`| rule_vertices |\<union>| AssumptionV |`| assm_vertices |\<union>| ConclusionV |`| conc_vertices"

definition preform_of_closed_form :: "'form \<Rightarrow> 'preform" where
  "preform_of_closed_form f = (SOME pf. subst undefined (freshen undefined pf) = f)"

fun nodeOf :: "Vertex \<Rightarrow> ('preform, 'rule) graph_node" where
  "nodeOf (ConclusionV n) = Conclusion (preform_of_closed_form (conc_forms |!| n))"
| "nodeOf (RuleV (i,is)) = Rule (fst (fromRule (snd (root (tree_at (ts (conc_forms |!| i)) is)))))"
| "nodeOf (AssumptionV (i,is)) = Assumption (preform_of_closed_form (snd (fst (root (tree_at (ts (conc_forms |!| i)) is)))))"

sublocale Tasked_Proof_Graph freshen fv ran_fv closed anyP subst pre_fv antecedent consequent fresh_vars rules assumptions conclusions
  vertices nodeOf
  sorry

end
