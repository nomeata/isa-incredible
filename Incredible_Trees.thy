theory Incredible_Trees
imports Natural_Deduction Incredible_Deduction
begin

lemma prefixeq_snocD: "prefixeq (xs@[x]) ys \<Longrightarrow> prefix xs ys"
  by (simp add: prefixI' prefix_order.dual_order.strict_trans1)

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

datatype ('form,'rule,'subst,'var)  itree =
    INode (iNodeOf': "('form, 'rule) graph_node")
          (iOutPort': "'form reg_out_port")
          (iAnnot: "nat")
          (iSubst: "'subst")
          (iAnts': "('form,'rule,'subst,'var) itree list")
  | HNode (iAnnot: "nat")
          (iSubst: "'subst")

fun iAnts where
   "iAnts (INode n p i s ants) = ants"
 | "iAnts (HNode i s) = []"

fun iNodeOf where
   "iNodeOf (INode n p i s ants) = n"
 | "iNodeOf (HNode i s) = Helper"

context Abstract_Formulas
begin
fun iOutPort where
   "iOutPort (INode n p i s ants) = p"
 | "iOutPort (HNode i s) = anyP"
end

type_synonym ('form, 'rule, 'subst) fresh_check = "('form, 'rule) graph_node \<Rightarrow> nat \<Rightarrow> 'subst \<Rightarrow> 'form entailment \<Rightarrow> bool"

context  Abstract_Task
begin

  inductive iwf :: "('form, 'rule, 'subst) fresh_check \<Rightarrow> ('form,'rule,'subst,'var) itree \<Rightarrow> 'form entailment \<Rightarrow> bool"
    for fc
    where
    iwf: "\<lbrakk>
       n \<in> sset nodes;
       Reg p |\<in>| outPorts n;
       list_all2 (\<lambda> ip t. iwf fc t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))))
                (inPorts' n) ants;
       fc n i s (\<Gamma> \<turnstile> c);
       c = subst s (freshen i p)
      \<rbrakk> \<Longrightarrow> iwf fc (INode n p i s ants) (\<Gamma> \<turnstile> c)"  
  | iwfH: "\<lbrakk>
       c |\<notin>| ass_forms;
       c |\<in>| \<Gamma>;
       c = subst s (freshen i anyP)
      \<rbrakk> \<Longrightarrow> iwf fc (HNode i s) (\<Gamma> \<turnstile> c)"  

lemma iwf_subst_freshen_outPort:
  "iwf lc ts ent \<Longrightarrow>
  snd ent = subst (iSubst ts) (freshen (iAnnot ts) (iOutPort ts))"
  by (auto elim: iwf.cases)



  inductive local_fresh_check :: "('form, 'rule, 'subst) fresh_check" where
    "\<lbrakk>\<And> ip f. ip |\<in>| inPorts n  \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenLC i ` (local_vars n ip) \<inter> lconsts f = {};
      \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> freshenLC i ` (local_vars n ip) \<inter> subst_lconsts s = {}
     \<rbrakk> \<Longrightarrow> local_fresh_check n i s (\<Gamma> \<turnstile> c)"

  abbreviation "local_iwf \<equiv> iwf local_fresh_check"
  
  
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
      have "local_iwf ?it (\<Gamma> \<turnstile> c)" by (auto intro!: iwf local_fresh_check.intros)

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

    note NatRule(5,6)
    ultimately
    have "local_iwf ?it ((\<Gamma> \<turnstile> subst s (freshen i c)))"
      by (intro iwf local_fresh_check.intros) (auto simp add: list_all2_map2 list_all2_same)
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


inductive it_pathsP :: "('form,'rule,'subst,'var) itree \<Rightarrow> nat list \<Rightarrow> bool"  where
   it_paths_Nil: "it_pathsP t []"
 | it_paths_Cons: "i < length (iAnts t) \<Longrightarrow> iAnts t ! i = t' \<Longrightarrow> it_pathsP t' is \<Longrightarrow> it_pathsP t (i#is)"

inductive_cases it_pathP_ConsE: "it_pathsP t (i#is)"

definition it_paths:: "('form,'rule,'subst,'var) itree \<Rightarrow> nat list set"  where
  "it_paths t = Collect (it_pathsP t)"

 lemma it_paths_eq [pred_set_conv]: "it_pathsP t = (\<lambda>x. x \<in> it_paths t)"
   by(simp add: it_paths_def)

 lemmas it_paths_intros [intro?] = it_pathsP.intros[to_set]
 lemmas it_paths_induct [consumes 1, induct set: it_paths] = it_pathsP.induct[to_set]
 lemmas it_paths_cases [consumes 1, cases set: it_paths] = it_pathsP.cases[to_set]
 lemmas it_paths_ConsE = it_pathP_ConsE[to_set]
 lemmas it_paths_simps = it_pathsP.simps[to_set]

 lemma [simp]: "[] \<in> it_paths t" by (rule it_paths_intros)

lemma it_paths_HNode[simp]: "it_paths (HNode i s) = {[]}"
  by (auto elim: it_paths_cases)

lemma it_paths_Union: "it_paths t \<subseteq> insert [] (Union (((\<lambda> (i,t). (op # i) ` it_paths t) ` set (List.enumerate (0::nat) (iAnts t)))))"
  apply (rule)
  apply (erule it_paths_cases)
  apply (auto intro!: bexI simp add: in_set_enumerate_eq)
  done

lemma finite_it_paths[simp]: "finite (it_paths t)"
  by (induction t) (auto intro!:  finite_subset[OF it_paths_Union]  simp add: in_set_enumerate_eq)
end

fun tree_at :: "('form,'rule,'subst,'var) itree \<Rightarrow> nat list \<Rightarrow> ('form,'rule,'subst,'var) itree" where
  "tree_at t [] = t"
| "tree_at t (i#is) = tree_at (iAnts t ! i) is"

context Abstract_Task
begin
lemma it_paths_SnocE[elim_format]:
  assumes "is @ [i] \<in> it_paths t"
  shows "is \<in> it_paths t \<and> i < length (iAnts (tree_at t is))"
using assms
by (induction "is" arbitrary: t)(auto intro!: it_paths_intros elim!: it_paths_ConsE)

fun isHNode where
  "isHNode (HNode _ _) = True"
 |"isHNode _ = False"


lemma it_paths_prefix:
  assumes "is \<in> it_paths t"
  assumes "prefix is' is"
  shows "is' \<in> it_paths t"
proof-
  from assms(2)
  obtain is'' where "is = is' @ is''" using prefixE' by blast
  from assms(1)[unfolded this]
  show ?thesis
    by(induction is' arbitrary: t) (auto elim!: it_paths_ConsE intro!: it_paths_intros)
qed

lemma it_paths_prefixeq:
  assumes "is \<in> it_paths t"
  assumes "prefixeq is' is"
  shows "is' \<in> it_paths t"
using assms it_paths_prefix  prefixI by fastforce

end


context Abstract_Task
begin
lemma it_path_SnocI:
  assumes "is \<in> it_paths t" 
  assumes "i < length (iAnts (tree_at t is))"
  (* assumes "iwf fc t ant" *)
  (* assumes "i |\<in>| inPorts (iNodeOf (tree_at t is))" *)
  shows "is @ [i] \<in> it_paths t"
  using assms
  apply (induction t arbitrary: "is" i)
  apply auto
  apply (case_tac "is")
  apply (auto intro: it_paths_intros elim!: it_paths_ConsE)
  done

lemma iwf_edge_match:
  assumes "iwf fc t ent"
  assumes "is@[i] \<in> it_paths t"
  shows "subst (iSubst (tree_at t (is@[i]))) (freshen (iAnnot (tree_at t (is@[i]))) (iOutPort (tree_at t (is@[i]))))
     = subst (iSubst (tree_at t is)) (freshen (iAnnot (tree_at t is)) (a_conc (inPorts' (iNodeOf (tree_at t is)) ! i)))"
  using assms
  apply (induction arbitrary: "is" i)
  apply (auto elim!:  it_paths_SnocE)
  apply (case_tac "is")
  apply (auto dest: list_all2_nthD2 intro: trans[OF iwf_subst_freshen_outPort[symmetric]])[1]
  apply (auto elim!: it_paths_ConsE)
  apply (drule(1) list_all2_nthD2)
  apply auto
  using it_path_SnocI
  apply blast
  done

lemma iwf_length_inPorts:
  assumes "iwf fc t ent"
  assumes "is \<in> it_paths t"
  shows "length (iAnts (tree_at t is)) \<le> length (inPorts' (iNodeOf (tree_at t is)))"
  using assms
  apply (induction arbitrary: "is" rule: iwf.induct)
  apply (case_tac "is")
  apply (auto elim!: it_paths_ConsE dest: list_all2_lengthD list_all2_nthD2)
  done

lemma iwf_length_inPorts_not_HNode:
  assumes "iwf fc t ent"
  assumes "is \<in> it_paths t"
  assumes "\<not> (isHNode (tree_at t is))"
  shows "length (iAnts (tree_at t is)) = length (inPorts' (iNodeOf (tree_at t is)))"
  using assms
  apply (induction arbitrary: "is" rule: iwf.induct)
  apply (case_tac "is")
  apply (auto elim!: it_paths_ConsE dest: list_all2_lengthD list_all2_nthD2)
  done

 

lemma iNodeOf_outPorts:
  "iwf fc t ent \<Longrightarrow> is \<in> it_paths t \<Longrightarrow> outPorts (iNodeOf (tree_at t is)) = {||} \<Longrightarrow> False"
  apply (induction arbitrary: "is" rule: iwf.induct)
  apply (case_tac "is")
  apply (auto elim!: it_paths_ConsE dest: list_all2_nthD2)
  done

lemma iNodeOf_tree_at:
  "iwf fc t ent \<Longrightarrow> is \<in> it_paths t \<Longrightarrow> iNodeOf (tree_at t is) \<in> sset nodes"
  apply (induction arbitrary: "is" rule: iwf.induct)
  apply (case_tac "is")
  apply (auto elim!: it_paths_ConsE dest: list_all2_nthD2)
  done

inductive_set hyps_along for t "is" where
 "prefixeq (is'@[i]) is \<Longrightarrow>
  i < length (inPorts' (iNodeOf (tree_at t is'))) \<Longrightarrow>
  hyps (iNodeOf (tree_at t is')) h = Some (inPorts' (iNodeOf (tree_at t is')) ! i) \<Longrightarrow>
  subst (iSubst (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h)) \<in> hyps_along t is"

lemma hyps_along_Nil[simp]: "hyps_along t [] = {}"
  by (auto simp add: hyps_along.simps)

lemma prefixeq_app_Cons_elim:
  assumes "prefixeq (xs@[y]) (z#zs)"
  obtains "xs = []" and "y = z"
   | xs' where "xs = z#xs'" and "prefixeq (xs'@[y]) zs"
using assms by (cases xs) auto

lemma prefixeq_app_Cons_simp:
  "prefixeq (xs@[y]) (z#zs) \<longleftrightarrow> (xs = [] \<and> y = z \<or> xs = z#tl xs \<and> prefixeq (tl xs@[y]) zs)"
 by (cases xs) auto

lemma hyps_along_Cons:
  assumes "iwf fc t ent"
  assumes "i#is \<in> it_paths t"
  shows "hyps_along t (i#is) =
    (\<lambda>h. subst (iSubst t) (freshen (iAnnot t) (labelsOut (iNodeOf t) h))) ` fset (hyps_for (iNodeOf t) (inPorts' (iNodeOf t) ! i))
    \<union> hyps_along (iAnts t ! i) is" (is "?S1 = ?S2 \<union> ?S3")
proof-
  from assms
  have "i < length (iAnts t)" and "is \<in> it_paths (iAnts t ! i)" 
    by (auto elim: it_paths_ConsE)
  let "?t'" = "iAnts t ! i"

  show ?thesis
  proof (rule; rule)
    fix x
    assume "x \<in> hyps_along t (i # is)"
    then obtain is' i' h where
      "prefixeq (is'@[i']) (i#is)"
      and "i' < length (inPorts' (iNodeOf (tree_at t is')))"
      and "hyps (iNodeOf (tree_at t is')) h = Some (inPorts' (iNodeOf (tree_at t is')) ! i')"
      and [simp]: "x = subst (iSubst (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h))"
    by (auto elim!: hyps_along.cases)
    from this(1)
    show "x \<in> ?S2 \<union> ?S3"
    proof(cases rule: prefixeq_app_Cons_elim)
      assume "is' = []" and "i' = i"
      with `hyps (iNodeOf (tree_at t is')) h = Some _`
      have "x \<in> ?S2" by auto
      thus ?thesis..
    next
      fix is''
      assume [simp]: "is' = i # is''" and "prefixeq (is'' @ [i']) is"
      have "tree_at t is' = tree_at ?t' is''" by simp

      note `prefixeq (is'' @ [i']) is`
           `i' < length (inPorts' (iNodeOf (tree_at t is')))`
           `hyps (iNodeOf (tree_at t is')) h = Some (inPorts' (iNodeOf (tree_at t is')) ! i')`
      from this[unfolded `tree_at t is' = tree_at ?t' is''`]
      have "subst (iSubst (tree_at (iAnts t ! i) is'')) (freshen (iAnnot (tree_at (iAnts t ! i) is'')) (labelsOut (iNodeOf (tree_at (iAnts t ! i) is'')) h))
          \<in> hyps_along (iAnts t ! i) is" by (rule hyps_along.intros)
      hence "x \<in> ?S3" by simp
      thus ?thesis..
    qed
  next
    fix x
    assume "x \<in> ?S2 \<union> ?S3"
    thus "x \<in> ?S1"
    proof
      have "prefixeq ([]@[i]) (i#is)" by simp
      moreover
      from `iwf _ t _`
      have "length (iAnts t) \<le> length (inPorts' (iNodeOf (tree_at t []))) "
        by cases (auto dest: list_all2_lengthD)
      with `i < _`
      have "i < length (inPorts' (iNodeOf (tree_at t [])))" by simp
      moreover
      assume "x \<in> ?S2"
      then obtain h where "h |\<in>| hyps_for (iNodeOf t) (inPorts' (iNodeOf t) ! i)"
        and [simp]: "x = subst (iSubst t) (freshen (iAnnot t) (labelsOut (iNodeOf t) h))" by auto
      from this(1)
      have "hyps (iNodeOf (tree_at t [])) h = Some (inPorts' (iNodeOf (tree_at t [])) ! i)" by simp
      ultimately
      have "subst (iSubst (tree_at t [])) (freshen (iAnnot (tree_at t [])) (labelsOut (iNodeOf (tree_at t [])) h)) \<in> hyps_along t (i # is)"
        by (rule hyps_along.intros)
      thus "x \<in> hyps_along t (i # is)" by simp
    next
      assume "x \<in> ?S3"
      thus "x \<in> ?S1"
        apply (auto simp add: hyps_along.simps)
        apply (rule_tac x = "i#is'" in exI)
        apply auto
        done
    qed
  qed
qed

lemma iwf_hyps_exist:
  assumes "iwf lc it (fst (root ts))"
  assumes "is \<in> it_paths it"
  assumes "tree_at it is = (HNode i s)"
  assumes "fst (fst (root ts)) |\<subseteq>| ass_forms"
  shows "subst s (freshen i anyP) \<in> hyps_along it is"
proof-
  from assms(1,2,3)
  have "subst s (freshen i anyP) \<in> hyps_along it is 
     \<or> subst s (freshen i anyP) |\<in>| fst (fst (root ts))
       \<and> subst s (freshen i anyP) |\<notin>| ass_forms"
  proof(induction arbitrary: "is" rule: iwf.induct)
    case (iwf n p  s' a' \<Gamma> ants c "is")

    have "iwf lc (INode n p a' s' ants) (\<Gamma> \<turnstile> c)"
      using iwf(1,2,3,4,5)
      by (auto intro!: iwf.intros elim!: list_all2_mono)

    show ?case
    proof(cases "is")
      case Nil
      with `tree_at (INode n p a' s' ants) is = HNode i s`
      show ?thesis by auto
    next
      case (Cons i' "is'")
      with `is \<in> it_paths (INode n p a' s' ants)`
      have "i' < length ants" and "is' \<in> it_paths (ants ! i')"
        by (auto elim: it_paths_ConsE)

      let ?\<Gamma>' = "(\<lambda>h. subst s' (freshen a' (labelsOut n h))) |`| hyps_for n (inPorts' n ! i')"

      from `tree_at (INode n p a' s' ants) is = HNode i s`
      have "tree_at (ants ! i') is' = HNode i s" using Cons by simp

      from  iwf.IH `i' < length ants`  `is' \<in> it_paths (ants ! i')` this
      have  "subst s (freshen i anyP) \<in> hyps_along (ants ! i') is'
        \<or> subst s (freshen i anyP) |\<in>| ?\<Gamma>' |\<union>| \<Gamma> \<and> subst s (freshen i anyP) |\<notin>| ass_forms"
        by (auto dest: list_all2_nthD2)
      moreover
      from  `is \<in> it_paths (INode n p a' s' ants)`
      have "hyps_along (INode n p a' s' ants) is = fset ?\<Gamma>' \<union> hyps_along (ants ! i') is'"
        using `is = _`
        by (simp add: hyps_along_Cons[OF `iwf lc (INode n p a' s' ants) (\<Gamma> \<turnstile> c)`])
      ultimately
      show ?thesis by auto
    qed
  next
    case (iwfH c  \<Gamma> s' i' "is")
    hence [simp]: "is = []" "i' = i" "s' = s" by simp_all
    from `c = subst s' (freshen i' anyP)` `c |\<in>| \<Gamma>` `c |\<notin>| ass_forms`
    show ?case by simp
  qed
  with assms(4)
  show ?thesis by blast
qed

fun fv_entailment :: "'form entailment \<Rightarrow> 'var set" where
  "fv_entailment (\<Gamma> \<turnstile> c) = Union (lconsts ` fset \<Gamma>) \<union> lconsts c"

definition hyp_port_for' :: "('form, 'rule, 'subst, 'a) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> nat list \<times> nat \<times> ('form, 'var) out_port" where
  "hyp_port_for' t is f = (SOME x.
   (case x of (is', i, h) \<Rightarrow> 
      prefixeq (is' @ [i]) is \<and>
      i < length (inPorts' (iNodeOf (tree_at t is'))) \<and>
      hyps (iNodeOf (tree_at t is')) h =  Some (inPorts' (iNodeOf (tree_at t is')) ! i) \<and>
      f = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h))
   ))"

lemma hyp_port_for_spec':
  assumes "f \<in> hyps_along t is"
  shows "(case hyp_port_for' t is f of (is', i, h) \<Rightarrow> 
      prefixeq (is' @ [i]) is \<and>
      i < length (inPorts' (iNodeOf (tree_at t is'))) \<and>
      hyps (iNodeOf (tree_at t is')) h =  Some (inPorts' (iNodeOf (tree_at t is')) ! i) \<and>
      f = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h)))"
using assms unfolding hyps_along.simps hyp_port_for'_def by -(rule someI_ex, blast)

definition hyp_port_path_for :: "('form, 'rule, 'subst, 'a) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> nat list"
  where "hyp_port_path_for t is f = fst (hyp_port_for' t is f)"
definition hyp_port_i_for ::  "('form, 'rule, 'subst, 'a) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> nat"
  where "hyp_port_i_for t is f = fst (snd (hyp_port_for' t is f))"
definition hyp_port_h_for :: "('form, 'rule, 'subst, 'a) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> ('form, 'var) out_port"
  where "hyp_port_h_for t is f = snd (snd (hyp_port_for' t is f))"

lemma hyp_port_prefixeq:
  assumes "f \<in> hyps_along t is"
  shows "prefixeq (hyp_port_path_for t is f@[hyp_port_i_for t is f]) is"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def by auto

lemma hyp_port_prefix:
  assumes "f \<in> hyps_along t is"
  shows "prefix (hyp_port_path_for t is f) is"
using hyp_port_prefixeq[OF assms] by (simp add: prefixI' prefix_order.dual_order.strict_trans1)

lemma hyp_port_it_paths:
  assumes "is \<in> it_paths t"
  assumes "f \<in> hyps_along t is"
  shows "hyp_port_path_for t is f \<in> it_paths t"
using assms by (rule it_paths_prefix[OF _ hyp_port_prefix] )


lemma hyp_port_hyps:
  assumes "f \<in> hyps_along t is"
  shows "hyps (iNodeOf (tree_at t (hyp_port_path_for t is f))) (hyp_port_h_for t is f) = Some (inPorts' (iNodeOf (tree_at t (hyp_port_path_for t is f))) ! hyp_port_i_for t is f)"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def hyp_port_h_for_def by auto

lemma hyp_port_outPort:
  assumes "f \<in> hyps_along t is"
  shows "(hyp_port_h_for t is f) |\<in>| outPorts (iNodeOf (tree_at t (hyp_port_path_for t is f)))"
using hyps_correct[OF hyp_port_hyps[OF assms]]..

lemma hyp_port_eq:
  assumes "f \<in> hyps_along t is"
  shows "f = subst (iSubst (tree_at t (hyp_port_path_for t is f))) (freshen (iAnnot (tree_at t (hyp_port_path_for t is f))) (labelsOut (iNodeOf (tree_at t (hyp_port_path_for t is f))) (hyp_port_h_for t is f)))"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def hyp_port_h_for_def by auto


lemma iwf_outPort: 
  assumes "iwf fc t ent"
  assumes "x \<in> it_paths t"
  shows "Reg (iOutPort (tree_at t x)) |\<in>| outPorts (iNodeOf (tree_at t x))"
using assms
  apply (induction arbitrary: x rule: iwf.induct)
  apply (case_tac x)
  apply (auto elim!: it_paths_ConsE dest: list_all2_nthD2)
  done

fun inits where
  "inits [] = [[]]"
| "inits (i#is) = [] # map (op # i) (inits is)"

lemma inits_Snoc[simp]:
  "inits (is@[i]) = inits is @ [is@[i]]"
by (induction "is") auto

lemma inits_eq_Snoc:
  "inits is = xs @ [x] \<longleftrightarrow> (is = [] \<and> xs = [] \<or> (\<exists> i is'. is = is'@[i] \<and> xs = inits is')) \<and> x = is"
by (cases "is" rule: rev_cases) auto

lemma in_set_inits[simp]: "is' \<in> set (inits is) \<longleftrightarrow> prefixeq is' is"
  by (induction "is'" arbitrary: "is"; case_tac "is"; auto)

text {*
  Rename all local constants.
  *}

(*
fun rename_local_consts :: "(var \<Rightarrow> var) \<Rightarrow> ('form,'rule,'subst,'var) itree \<Rightarrow> ('form,'rule,'subst,'var) itree"  where
    "rename_local_consts f (INode n p i s ants) = (INode n p i (subst_renameLCs f s) (ants)"
  | "rename_local_consts f (HNode i s) = (HNode i s)"

*)



  text {*
  Like local_iwf, but every name occuring in a substitution has
  is either in the conclusion of the rule, or created by this rule.
  *}

  inductive global_fresh_check :: "('form, 'rule, 'subst) fresh_check" where
    "subst_lconsts s \<subseteq> fv_entailment (\<Gamma> \<turnstile> c) \<union> range (freshenLC i) \<Longrightarrow> global_fresh_check n i s (\<Gamma> \<turnstile> c)"

  abbreviation "global_iwf \<equiv> iwf global_fresh_check"

  definition globalize :: "('form,'rule,'subst,'var) itree \<Rightarrow> ('form,'rule,'subst,'var) itree" where
    "globalize = undefined"


  lemma globalized:
    assumes "tfinite t" and "wf t"
    assumes "local_iwf it' (fst (root t))"
    shows "global_iwf (globalize it') (fst (root t))"
    sorry

  lemma it_paths_globalize:
    "it_paths (globalize it) = it_paths it"
    sorry

end   

end
