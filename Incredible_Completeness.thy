theory Incredible_Completeness
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

datatype ('preform,'rule,'subst,'var)  itree =
    INode (iNodeOf': "('preform, 'rule) graph_node")
          (iOutPort': "'preform reg_out_port")
          (iAnnot: "nat")
          (iSubst: "'subst")
          (iAnts': "('preform, 'var) in_port \<rightharpoonup> ('preform,'rule,'subst,'var) itree")
  | HNode (iAnnot: "nat")
          (iSubst: "'subst")

fun iAnts where
   "iAnts (INode n p i s ants) = ants"
 | "iAnts (HNode i s) = empty"

fun iNodeOf where
   "iNodeOf (INode n p i s ants) = n"
 | "iNodeOf (HNode i s) = Helper"

context Abstract_Formulas
begin
fun iOutPort where
   "iOutPort (INode n p i s ants) = p"
 | "iOutPort (HNode i s) = anyP"
end

context Abstract_Task
begin
  inductive iwf :: "('preform,'rule,'subst,'var) itree \<Rightarrow> 'form entailment \<Rightarrow> bool" where
    iwf: "\<lbrakk>
       n \<in> sset nodes;
       Reg p |\<in>| outPorts n;
       \<And> ip. ip |\<in>| inPorts n \<Longrightarrow>
          (\<exists> t. ants ip = Some t \<and>
              iwf t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))));
       \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenV i ` (local_vars n ip) \<inter> fv f = {};
       \<And> ip. ip |\<in>| inPorts n  \<Longrightarrow> freshenV i ` (local_vars n ip) \<inter> ran_fv s = {};
       c = subst s (freshen i (labelsOut n (Reg p :: (('preform, 'var) out_port))))
      \<rbrakk> \<Longrightarrow> iwf (INode n p i s ants) (\<Gamma> \<turnstile> c)"  
  | iwfH: "\<lbrakk>
       c |\<notin>| ass_forms;
       c |\<in>| \<Gamma>;
       c = subst s (freshen i anyP)
      \<rbrakk> \<Longrightarrow> iwf (HNode i s) (\<Gamma> \<turnstile> c)"  


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
  then obtain its where its: "\<And> t'. t' |\<in>| cont t \<Longrightarrow> iwf (its t') (fst (root t'))" by metis

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

      from `c \<in> set assumptions`
      have "iwf ?it (\<Gamma> \<turnstile> con)" by (auto intro!: iwf)
      thus ?thesis unfolding Axiom..
    next
      case False
      obtain s where [simp]: "subst s (freshen undefined anyP) = con" by atomize_elim (rule anyP_is_any)
  
      let "?it" = "HNode undefined s ::  ('preform, 'rule, 'subst, 'var) itree"
  
      from  `con |\<in>| \<Gamma>` False
      have "iwf ?it (\<Gamma> \<turnstile> con)" by (auto intro: iwfH)
      thus ?thesis unfolding Axiom..
    qed
  next
  case (NatRule rule c ants \<Gamma> i s)
    from `natEff_Inst rule c ants`
    have "snd rule = c"  and [simp]: "f_antecedent (fst rule) = ants" and "c \<in> set (consequent (fst rule))"
      by (auto simp add: natEff_Inst.simps)  

    from `(fst \<circ> root) |\`| cont t = (\<lambda>ant. (\<lambda>p. subst s (freshen i p)) |\`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant))) |\`| ants`
    obtain to_t where "\<And> ant. ant |\<in>| ants \<Longrightarrow> to_t ant |\<in>| cont t \<and> (fst \<circ> root) (to_t ant) = ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
      by (rule fimage_eq_to_f) (rule that)
    hence to_t_in_cont: "\<And> ant. ant |\<in>| ants \<Longrightarrow> to_t ant |\<in>| cont t"
      and to_t_root: "\<And> ant. ant |\<in>| ants \<Longrightarrow>  fst (root (to_t ant)) = ((\<lambda>p. subst s (freshen i p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen i (a_conc ant)))"
      by auto

    let "?it" = "INode (Rule (fst rule)) c i s (\<lambda> ant. if ant |\<in>| ants then Some (its (to_t ant)) else None) ::  ('preform, 'rule, 'subst, 'var) itree"

    from `snd (root t) \<in> R`
    have "fst rule \<in> sset rules"
      unfolding NatRule
      by (auto simp add: stream.set_map n_rules_def no_empty_conclusions )
    moreover
    from `c \<in> set (consequent (fst rule))`
    have "c |\<in>| f_consequent (fst rule)" by (simp add: f_consequent_def)
    moreover
    { fix ant
      assume "ant |\<in>| ants"
      from its[OF to_t_in_cont[OF this]]
      have "iwf (its (to_t ant)) (fst (root (to_t ant)))".
      also have "fst (root (to_t ant)) =
        ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst rule)) h))) |`| hyps_for (Rule (fst rule)) ant |\<union>| \<Gamma>
         \<turnstile> subst s (freshen i (a_conc ant)))"
        by (auto simp add: to_t_root `ant |\<in>| ants`)
      finally
      have "iwf (its (to_t ant))
           ((\<lambda>h. subst s (freshen i (labelsOut (Rule (fst rule)) h))) |`| hyps_for (Rule (fst rule)) ant |\<union>|
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
    have "iwf ?it (\<Gamma> \<turnstile> con)" by (auto intro!: iwf)
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
       n \<in> sset nodes;
       Reg p |\<in>| outPorts n;
       \<And> ip. ip |\<in>| inPorts n \<Longrightarrow>
          (\<exists> t. ants ip = Some t \<and>
              iwf' t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))));
       ran_fv s \<subseteq> fv_entailment (\<Gamma> \<turnstile> c) \<union> range (freshenV i);
       c = subst s (freshen i (labelsOut n (Reg p :: (('preform, 'var) out_port))))
      \<rbrakk> \<Longrightarrow> iwf' (INode n p i s ants) (\<Gamma> \<turnstile> c)"  
  | iwf'H: "\<lbrakk>
       c |\<notin>| ass_forms;
       c |\<in>| \<Gamma>;
       c = subst s (freshen i anyP)
      \<rbrakk> \<Longrightarrow> iwf' (HNode i s) (\<Gamma> \<turnstile> c)"  

lemma iwf'_subst_freshen_outPort:
  "iwf' ts ent \<Longrightarrow>
  snd ent = subst (iSubst ts) (freshen (iAnnot ts) (iOutPort ts))"
  by (auto elim: iwf'.cases)



lemma iwf'_to_it:
  assumes "tfinite t" and "wf t"
  shows "iwf' (to_it t) (fst (root t))"
sorry


inductive it_pathsP :: "('preform,'rule,'subst,'var) itree \<Rightarrow> ('preform, 'var) in_port list \<Rightarrow> bool"  where
   it_paths_Nil: "it_pathsP t []"
 | it_paths_Cons: "i |\<in>| inPorts (iNodeOf t) \<Longrightarrow> iAnts t i = Some t' \<Longrightarrow> it_pathsP t' is \<Longrightarrow> it_pathsP t (i#is)"

inductive_cases it_pathP_ConsE: "it_pathsP t (i#is)"

definition it_paths:: "('preform,'rule,'subst,'var) itree \<Rightarrow> ('preform, 'var) in_port list set"  where
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

lemma it_paths_Union: "it_paths t \<subseteq> insert [] (Union (fset ((\<lambda> i. case iAnts t i of Some t \<Rightarrow> (op # i) ` it_paths t | None \<Rightarrow> {}) |`| (inPorts (iNodeOf t)))))"
  apply (rule)
  apply (subst (asm) it_paths_simps)
  apply (fastforce split: prod.split simp add: fmember.rep_eq)
  done

lemma finite_it_paths[simp]: "finite (it_paths t)"
  by (induction t) (rule finite_subset[OF it_paths_Union], fastforce split: option.split intro: range_eqI)+
end

fun tree_at :: "('preform,'rule,'subst,'var) itree \<Rightarrow> ('preform, 'var) in_port list \<Rightarrow> ('preform,'rule,'subst,'var) itree" where
  "tree_at t [] = t"
| "tree_at t (i#is) = tree_at (the (iAnts t i)) is"

context Abstract_Task
begin
lemma it_path_SnocE[elim_format]:
  assumes "is @ [i] \<in> it_paths t"
  shows "is \<in> it_paths t \<and> i |\<in>| inPorts (iNodeOf (tree_at t is))"
using assms
by (induction "is" arbitrary: t)(auto intro!: it_paths_intros elim!: it_paths_ConsE)

fun isHNode where
  "isHNode (HNode _ _) = True"
 |"isHNode _ = False"

lemma it_path_SnocI:
  assumes "iwf' t ant"
  assumes "is \<in> it_paths t" 
  assumes "\<not> isHNode (tree_at t is)"
  assumes "i |\<in>| inPorts (iNodeOf (tree_at t is))"
  shows "is @ [i] \<in> it_paths t"
  using assms
  apply (induction arbitrary: "is" i)
  apply auto
  apply (case_tac "is")
  apply (force intro: it_paths_intros elim!: it_paths_ConsE)+
  done

lemma iwf'_edge_match:
  assumes "iwf' t ent"
  assumes "is@[i] \<in> it_paths t"
  shows "subst (iSubst (tree_at t (is@[i]))) (freshen (iAnnot (tree_at t (is@[i]))) (iOutPort (tree_at t (is@[i]))))
     = subst (iSubst (tree_at t is)) (freshen (iAnnot (tree_at t is)) (a_conc i))"
  using assms
  apply (induction arbitrary: "is" i)
  apply (case_tac "is")
  apply (force elim!: it_paths_ConsE intro: trans[OF iwf'_subst_freshen_outPort[symmetric]])+
  done


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
end


type_synonym ('preform, 'var) vertex = "('preform \<times> ('preform, 'var) in_port list)"
type_synonym ('preform, 'var) edge'' = "(('preform, 'var) vertex, 'preform, 'var) edge'"


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

lemma to_form_conc_forms[simp]: "to_form a |\<in>| conc_forms \<longleftrightarrow> a \<in> set conclusions"
proof
  assume "a \<in> set conclusions"
  thus "to_form a |\<in>| conc_forms" by (rule subst_freshen_in_conc_formsI)
next
  assume "to_form a |\<in>| conc_forms"
  then obtain a' where "a' \<in> set conclusions" and "to_form a = to_form a'"
    by (auto simp add: conc_forms_def)
  thus "a \<in> set conclusions" using conclusions_closed closed_eq by metis
qed

abbreviation it where
  "it c \<equiv> to_it (ts (to_form c))"

lemma iwf'_it:
  assumes "c \<in> set conclusions"
  shows "iwf' (it c) (fst (root (ts (to_form c))))"
  using assms by (auto intro!: iwf'_to_it ts_finite ts_wf)

definition vertices :: "('preform, 'var) vertex fset"  where
  "vertices = Abs_fset (Union ( set (map (\<lambda> c. insert (c, []) ((\<lambda> p. (c, plain_ant c # p)) ` (it_paths (it c))))  conclusions)))"

lemma mem_vertices: "v |\<in>| vertices \<longleftrightarrow>  (fst v \<in> set conclusions \<and> (snd v = [] \<or> snd v \<in> (op # (plain_ant (fst v))) ` it_paths (it (fst v))))"
  unfolding vertices_def fmember.rep_eq ffUnion.rep_eq 
  by (cases v) (auto simp add: Abs_fset_inverse Bex_def)

lemma none_vertices[simp]: "(c, []) |\<in>| vertices \<longleftrightarrow> c \<in> set conclusions"
  by (simp add: mem_vertices)

lemma some_vertices[simp]: "(c, i#is) |\<in>| vertices \<longleftrightarrow> c \<in> set conclusions \<and> i = plain_ant c \<and> is \<in> it_paths (it c)"
  by (auto simp add: mem_vertices)

lemma vertices_cases[consumes 1, case_names None Some]:
  assumes "v |\<in>| vertices"
  obtains c where "c \<in> set conclusions" and "v = (c, [])"
      |   c "is" where "c \<in> set conclusions" and "is \<in> it_paths (it c)" and "v = (c, plain_ant c#is)"
using assms by (cases v; rename_tac "is"; case_tac "is"; auto)

lemma vertices_induct[consumes 1, case_names None Some]:
  assumes "v |\<in>| vertices"
  assumes "\<And> c. c \<in> set conclusions \<Longrightarrow> P (c, [])"
  assumes "\<And> c is . c \<in> set conclusions \<Longrightarrow> is \<in> it_paths (it c) \<Longrightarrow> P (c, plain_ant c#is)"
  shows "P v"
using assms by (cases v; rename_tac "is"; case_tac "is"; auto)


definition preform_of_closed_form :: "'form \<Rightarrow> 'preform" where
  "preform_of_closed_form f = (SOME pf. subst undefined (freshen undefined pf) = f)"

fun nodeOf :: "('preform, 'var) vertex \<Rightarrow> ('preform, 'rule) graph_node" where
  "nodeOf (pf, []) = Conclusion pf"
| "nodeOf (pf, i#is) = iNodeOf (tree_at (it pf) is)"

fun inst where
  "inst (c,[]) = undefined"
 |"inst (c, i#is) = iSubst (tree_at (it c) is)" 


lemma iNodeOf_outPorts:
  "iwf' t ent \<Longrightarrow> x \<in> it_paths t \<Longrightarrow> outPorts (iNodeOf (tree_at t x)) = {||} \<Longrightarrow> False"
  apply (induction arbitrary: x rule: iwf'.induct)
  apply (case_tac x)
  apply (auto elim!: it_paths_ConsE)
  apply force
  done

lemma terminal_is_nil[simp]: "v |\<in>| vertices \<Longrightarrow> outPorts (nodeOf v) = {||} \<longleftrightarrow> snd v = []"
 apply (induction v rule: nodeOf.induct)
 apply auto
 apply (erule (1) iNodeOf_outPorts[rotated])
 apply (erule iwf'_it)
 done

lemma iNodeOf_tree_at:
  "iwf' t ent \<Longrightarrow> x \<in> it_paths t \<Longrightarrow> iNodeOf (tree_at t x) \<in> sset nodes"
  apply (induction arbitrary: x rule: iwf'.induct)
  apply (case_tac x)
  apply (auto elim!: it_paths_ConsE)
  apply force
  done

sublocale Vertex_Graph nodes inPorts outPorts vertices nodeOf.


definition edge_from :: "'preform \<Rightarrow> ('preform, 'var) in_port list => (('preform, 'var) vertex \<times> ('preform,'var) out_port)" where 
  "edge_from c is = ((c, plain_ant c # is),  Reg (iOutPort (tree_at (it c) is)))"

lemma fst_edge_from[simp]: "fst (edge_from c is) = (c, plain_ant c # is)"
  by (simp add: edge_from_def)

definition edge_to :: "'preform \<Rightarrow> ('preform, 'var) in_port list => (('preform, 'var) vertex \<times> ('preform,'var) in_port)"  where
 "edge_to c is =
    (case rev is of   []   \<Rightarrow> ((c, []),            plain_ant c)
                    | i#is \<Rightarrow> ((c, plain_ant c # (rev is)), i))"

lemma edge_to_Nil[simp]: "edge_to c [] = ((c, []), plain_ant c)"
  by (simp add: edge_to_def)

lemma edge_to_Snoc[simp]: "edge_to c (is@[i]) = ((c, plain_ant c # is), i)"
  by (simp add: edge_to_def)

definition edge_at :: "'preform \<Rightarrow> ('preform, 'var) in_port list => ('preform, 'var) edge''"  where
   "edge_at c i = (edge_from c i, edge_to c i)"

lemma fst_edge_at[simp]: "fst (edge_at c i) = edge_from c i" by (simp add: edge_at_def)
lemma snd_edge_at[simp]: "snd (edge_at c i) = edge_to c i" by (simp add: edge_at_def)

inductive_set hyps_along for t "is" where
 "prefixeq (is'@[i]) is \<Longrightarrow>
  hyps (iNodeOf (tree_at t is')) h = Some i \<Longrightarrow>
  subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h)) \<in> hyps_along t is"

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
  assumes "i#is \<in> it_paths t"
  shows "hyps_along t (i#is) =
    (\<lambda>h. subst (iSubst t) (freshen (iAnnot t) (labelsOut (iNodeOf t) h))) ` fset (hyps_for (iNodeOf t) i)
    \<union> hyps_along (the (iAnts t i)) is" (is "?S1 = ?S2 \<union> ?S3")
proof-
  from assms
  obtain t' where "i |\<in>| inPorts (iNodeOf t)" and [simp]: "iAnts t i = Some t'" and "is \<in> it_paths t'"
    by (auto elim: it_paths_ConsE)

  show ?thesis
  proof (rule; rule)
    fix x
    assume "x \<in> hyps_along t (i # is)"
    then obtain is' i' h where
      "prefixeq (is'@[i']) (i#is)"
      and "hyps (iNodeOf (tree_at t is')) h = Some i'"
      and [simp]: "x = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h))"
    by (auto elim: hyps_along.cases)
    from this(1)
    show "x \<in> ?S2 \<union> ?S3"
    proof(cases rule: prefixeq_app_Cons_elim)
      assume "is' = []" and "i' = i"
      with `hyps (iNodeOf (tree_at t is')) h = Some i'`
      have "x \<in> ?S2" by auto
      thus ?thesis..
    next
      fix is''
      assume [simp]: "is' = i # is''" and "prefixeq (is'' @ [i']) is"

      from `hyps (iNodeOf (tree_at t is')) h = Some i'`
      have "hyps (iNodeOf (tree_at t' is'')) h = Some i'" by simp

      from hyps_along.intros[OF `prefixeq (is'' @ [i']) is` this]
      have "subst (iSubst (tree_at t' is'')) (freshen (iAnnot (tree_at t' is'')) (labelsOut (iNodeOf (tree_at t' is'')) h))  \<in> hyps_along t' is".
      hence "x \<in> ?S3" by simp
      thus ?thesis..
    qed
  next
    fix x
    assume "x \<in> ?S2 \<union> ?S3"
    thus "x \<in> ?S1"
    proof
      have "prefixeq ([]@[i]) (i#is)" by simp
      
      assume "x \<in> ?S2"
      then obtain h where "h |\<in>| hyps_for (iNodeOf t) i"
        and [simp]: "x = subst (iSubst t) (freshen (iAnnot t) (labelsOut (iNodeOf t) h))" by auto
      from this(1)
      have "hyps (iNodeOf (tree_at t [])) h = Some i" by simp
      
      from hyps_along.intros[OF `prefixeq ([]@[i]) (i#is)` this]
      show "x \<in> hyps_along t (i # is)" by simp
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
      
lemma hyps_exist:
  assumes "c \<in> set conclusions"
  assumes "is \<in> it_paths (it c)"
  assumes "tree_at (it c) is = (HNode i s)"
  shows "subst s (freshen i anyP) \<in> hyps_along (it c) is"
proof-
  from assms(1)
  have "iwf' (it c) (fst (root (ts (to_form c))))" by (rule iwf'_it)
  note this assms(2,3)
  hence "subst s (freshen i anyP) \<in> hyps_along (it c) is 
     \<or> subst s (freshen i anyP) |\<in>| fst (fst (root (ts (to_form c))))
       \<and> subst s (freshen i anyP) |\<notin>| ass_forms"
  proof(induction arbitrary: "is" rule: iwf'.induct)
    case (iwf' n p ants s' i' \<Gamma> c "is")
   
    show ?case
    proof(cases "is")
      case Nil
      with `tree_at (INode n p i' s' ants) is = HNode i s`
      show ?thesis by auto
    next
      case (Cons ip "is'")
      with `is \<in> it_paths (INode n p i' s' ants)`
      obtain it where "ip |\<in>| inPorts n" and [simp]: "ants ip = Some it" and "is' \<in> it_paths it"
        by (auto elim: it_paths_ConsE)

      let ?\<Gamma>' = "(\<lambda>h. subst s' (freshen i' (labelsOut n h))) |`| hyps_for n ip"
      
      from `tree_at (INode n p i' s' ants) is = HNode i s`
      have "tree_at it is' = HNode i s" using Cons `ants ip = Some it` by simp

      from  iwf'.IH[OF `ip |\<in>| _`] `ants ip = Some it` `is' \<in> it_paths it` this
      have  "subst s (freshen i anyP) \<in> hyps_along it is'
        \<or> subst s (freshen i anyP) |\<in>| ?\<Gamma>' |\<union>| \<Gamma> \<and> subst s (freshen i anyP) |\<notin>| ass_forms"
        by auto
      moreover
      from  `is \<in> it_paths (INode n p i' s' ants)`
      have "hyps_along (INode n p i' s' ants) is = fset ?\<Gamma>' \<union> hyps_along it is'"
        using `is = _` by (simp add: hyps_along_Cons)
      ultimately
      show ?thesis by auto
    qed
  next
    case (iwf'H c  \<Gamma> s' i' "is")
    hence [simp]: "is = []" "i' = i" "s' = s" by simp_all
    from `c = subst s' (freshen i' anyP)` `c |\<in>| \<Gamma>` `c |\<notin>| ass_forms`
    show ?case by simp
  qed
  moreover
  have "fst (fst (root (ts (to_form c)))) |\<subseteq>| ass_forms"
    by (simp add: assms(1) ts_context)
  ultimately
  show ?thesis by blast
qed


definition hyp_port_for' where
  "hyp_port_for' t is f = (SOME x.
   (case x of (is', i, h) \<Rightarrow> 
      prefixeq (is' @ [i]) is \<and>
      hyps (iNodeOf (tree_at t is')) h = Some i \<and>
      f = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h))
   ))"

lemma hyp_port_for_spec':
  assumes "f \<in> hyps_along t is"
  shows "(case hyp_port_for' t is f of (is', i, h) \<Rightarrow> 
      prefixeq (is' @ [i]) is \<and>
      hyps (iNodeOf (tree_at t is')) h = Some i \<and>
      f = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h)))"
using assms unfolding hyps_along.simps hyp_port_for'_def by -(rule someI_ex, blast)

definition hyp_port_path_for where "hyp_port_path_for t is f = fst (hyp_port_for' t is f)"
definition hyp_port_i_for where "hyp_port_i_for t is f = fst (snd (hyp_port_for' t is f))"
definition hyp_port_h_for where "hyp_port_h_for t is f = snd (snd (hyp_port_for' t is f))"

lemma hyp_port_prefixeq:
  assumes "f \<in> hyps_along t is"
  shows "prefixeq (hyp_port_path_for t is f@[hyp_port_i_for t is f]) is"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def by auto

lemma hyp_port_prefix:
  assumes "f \<in> hyps_along t is"
  shows "prefix (hyp_port_path_for t is f) is"
using hyp_port_prefixeq[OF assms] by (simp add: prefixI' prefix_order.dual_order.strict_trans1)

lemma hyp_port_hyps:
  assumes "f \<in> hyps_along t is"
  shows "hyps (iNodeOf (tree_at t (hyp_port_path_for t is f))) (hyp_port_h_for t is f) = Some (hyp_port_i_for t is f)"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def hyp_port_h_for_def by auto

lemma hyp_port_outPort:
  assumes "f \<in> hyps_along t is"
  shows "(hyp_port_h_for t is f) |\<in>| outPorts (iNodeOf (tree_at t (hyp_port_path_for t is f)))"
using hyps_correct[OF hyp_port_hyps[OF assms]]..

lemma hyp_port_eq:
  assumes "f \<in> hyps_along t is"
  shows "f = subst (iSubst (tree_at t (hyp_port_path_for t is f))) (freshen (iAnnot (tree_at t (hyp_port_path_for t is f))) (labelsOut (iNodeOf (tree_at t (hyp_port_path_for t is f))) (hyp_port_h_for t is f)))"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def hyp_port_h_for_def by auto



definition hyp_edge_to where
  "hyp_edge_to c is = ((c, plain_ant c # is),  plain_ant anyP)"

definition hyp_edge_from where
  "hyp_edge_from c is n s = 
    ((c, plain_ant c # hyp_port_path_for (it c) is (subst s (freshen n anyP))), hyp_port_h_for (it c) is (subst s (freshen n anyP)))"

definition hyp_edge_at where
  "hyp_edge_at c is n s = (hyp_edge_from c is n s, hyp_edge_to c is)"

lemma fst_hyp_edge_at[simp]:
  "fst (hyp_edge_at c is n s) = hyp_edge_from c is n s" by (simp add:hyp_edge_at_def) 
lemma snd_hyp_edge_at[simp]:
  "snd (hyp_edge_at c is n s) = hyp_edge_to c is" by (simp add:hyp_edge_at_def)

inductive_set edges where
  regular_edge: "c \<in> set conclusions \<Longrightarrow> is \<in> it_paths (it c) \<Longrightarrow> edge_at c is \<in> edges"
  | hyp_edge: "c \<in> set conclusions \<Longrightarrow> is \<in> it_paths (it c) \<Longrightarrow> tree_at (it c) is = HNode n s \<Longrightarrow> hyp_edge_at c is n s \<in> edges"

sublocale Pre_Port_Graph nodes inPorts outPorts vertices nodeOf edges.

lemma iwf'_outPort: 
  assumes "iwf' t ent"
  assumes "x \<in> it_paths t"
  shows "Reg (iOutPort (tree_at t x)) |\<in>| outPorts (iNodeOf (tree_at t x))"
using assms
  apply (induction arbitrary: x rule: iwf'.induct)
  apply (case_tac x)
  apply (auto elim!: it_paths_ConsE)
  apply force
  done

lemma edge_from_valid_out_port:
  assumes "p \<in> it_paths (it c)"
  assumes "c \<in> set conclusions"
  shows "valid_out_port (edge_from c p)"
using assms
by (auto simp add: edge_from_def intro: iwf'_outPort iwf'_it)

lemma edge_to_valid_in_port:
  assumes "p \<in> it_paths (it c)"
  assumes "c \<in> set conclusions"
  shows "valid_in_port (edge_to c p)"
using assms
by (auto simp add: edge_to_def split: list.split elim!: it_path_SnocE)

lemma hyp_edge_from_valid_out_port:
  assumes "is \<in> it_paths (it c)"
  assumes "c \<in> set conclusions"
  assumes "tree_at (it c) is = HNode n s"
  shows "valid_out_port (hyp_edge_from c is n s)"
using assms
by(auto simp add: hyp_edge_from_def intro: hyp_port_outPort it_paths_prefix hyp_port_prefix  hyps_exist)

lemma hyp_edge_to_valid_in_port:
  assumes "is \<in> it_paths (it c)"
  assumes "c \<in> set conclusions"
  assumes "tree_at (it c) is = HNode n s"
  shows "valid_in_port (hyp_edge_to c is)"
using assms by (auto simp add: hyp_edge_to_def)



inductive scope' where
  "c \<in> set conclusions \<Longrightarrow>
   is' \<in> (op # (plain_ant c)) ` it_paths (it c) \<Longrightarrow>
   prefixeq (is@[i]) is' \<Longrightarrow> 
   scope' (c, is) i (c, is')"

inductive_simps scope_simp: "scope' v i v'"
inductive_cases scope_cases: "scope' v i v'"

lemma scope_valid:
  "scope' v i v' \<Longrightarrow> v' |\<in>| vertices"
by (auto elim: scope_cases)

lemma scope_valid_inport:
  "valid_in_port (v, i) \<Longrightarrow> v' |\<in>| vertices \<Longrightarrow> scope' v i v' \<longleftrightarrow> fst v = fst v' \<and> prefixeq (snd v@[i]) (snd v')"
by (cases v; cases v') (auto simp add: scope'.simps mem_vertices)

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

definition terminal_path_from :: "'preform \<Rightarrow> ('preform, 'var) in_port list => ('preform, 'var) edge'' list" where
   "terminal_path_from c is = map (edge_at c) (rev (inits is))"

lemma terminal_path_from_Nil[simp]:
  "terminal_path_from c [] = [edge_at c []]"
  by (simp add: terminal_path_from_def)

lemma terminal_path_from_Snoc[simp]:
  "terminal_path_from c (is @ [i]) = edge_at c (is@[i]) # terminal_path_from c is"
  by (simp add: terminal_path_from_def)

lemma path_terminal_path_from:
  "c \<in> set conclusions \<Longrightarrow>
  is \<in> it_paths (it c) \<Longrightarrow>
  path (c, plain_ant c # is) (c, []) (terminal_path_from c is)"
by (induction "is" rule: rev_induct)
   (auto simp add: path_cons_simp intro!: regular_edge elim: it_path_SnocE)

lemma edge_step:
  assumes "(((a, b), ba), ((aa, bb), bc)) \<in> edges"
  obtains "a = aa" and "b = bb@[bc]" and "hyps (nodeOf (a, b)) ba = None"
  | i where "a = aa" and "prefixeq (b@[i]) bb" and "hyps (nodeOf (a, b)) ba = Some i"
using assms
proof(cases rule: edges.cases[consumes 1, case_names Reg Hyp])
  case (Reg c "is")
  hence "a = aa" and "b = bb@[bc]" and "hyps (nodeOf (a, b)) ba = None"
    by (auto elim!: edges.cases simp add: edge_at_def edge_from_def edge_to_def split: list.split list.split_asm)
  thus thesis by (rule that)
next
  case (Hyp c "is" n s)
  hence "a = aa" and "prefixeq (b@[hyp_port_i_for (it c) is (subst s (freshen n anyP))]) bb" and
    "hyps (nodeOf (a, b)) ba = Some (hyp_port_i_for (it c) is (subst s (freshen n anyP)))"
  by (auto simp add: edge_at_def edge_from_def edge_to_def hyp_edge_at_def hyp_edge_to_def hyp_edge_from_def
      intro: hyp_port_prefixeq hyps_exist hyp_port_hyps)
  thus thesis by (rule that)
qed

lemma path_has_prefixes:
  assumes "path v v' pth"
  assumes "snd v' = []"
  assumes "prefixeq (is' @ [i]) (snd v)"
  shows "((fst v, is'), i) \<in> snd ` set pth"
  using assms
  by (induction rule: path.induct)(auto elim!: edge_step dest: prefixeq_snocD)


lemma in_scope: "valid_in_port (v', p') \<Longrightarrow> v \<in> scope (v', p') \<longleftrightarrow> scope' v' p' v"
proof
  assume "v \<in> scope (v', p')"
  hence "v |\<in>| vertices" and "\<And> pth t.  path v t pth \<Longrightarrow> terminal_vertex t \<Longrightarrow> (v', p') \<in> snd ` set pth"
    by (auto simp add: scope.simps)
  from this
  show "scope' v' p' v"
  proof (induction  rule: vertices_induct)
    case (None c)
    from None(2)[of "(c, [])" "[]", simplified, OF None(1)]
    have False.
    thus "scope' v' p' (c, [])"..
  next
    case (Some c "is")

    from `c \<in> set conclusions` `is \<in> it_paths (it c)`
    have "path (c, plain_ant c # is) (c, []) (terminal_path_from c is)"
      by (rule path_terminal_path_from)
    moreover
    from `c \<in> set conclusions`
    have "terminal_vertex (c, [])" by simp
    ultimately
    have "(v', p') \<in> snd ` set (terminal_path_from c is)"
      by (rule Some(3))
    hence "(v',p') \<in> set (map (edge_to c) (inits is))"
      unfolding terminal_path_from_def by auto
    then obtain is' where "prefixeq is' is" and "(v',p') = edge_to c is'"
      by auto
    show "scope' v' p' (c, plain_ant c # is)"
    proof(cases "is'" rule: rev_cases)
      case Nil
      with `(v',p') = edge_to c is'`
      have "v' = (c, [])" and "p' = plain_ant c"
        by (auto simp add: edge_to_def)
      with `c \<in> set conclusions` `is \<in> it_paths (it c)`
      show ?thesis  by (auto intro!: scope'.intros)
    next
      case (snoc is'' i)
      with `(v',p') = edge_to c is'`
      have "v' = (c, plain_ant c # is'')" and "p' = i"
        by (auto simp add: edge_to_def)
      with `c \<in> set conclusions` `is \<in> it_paths (it c)` `prefixeq is' is`[unfolded snoc]
      show ?thesis
        by (auto intro!: scope'.intros)
    qed
  qed
next
  assume "valid_in_port (v', p')"
  assume "scope' v' p' v"
  then obtain c is' "is" where
    "v' = (c, is')" and "v = (c, is)" and "c \<in> set conclusions" and
    "is \<in> op # (plain_ant c) ` it_paths (it c)" and  "prefixeq (is' @ [p']) is"
    by (auto simp add: scope'.simps)

  from `scope' v' p' v`
  have "(c, is) |\<in>| vertices" unfolding `v = _` by (rule scope_valid)
  hence "(c, is) \<in> scope ((c, is'), p')"
  proof(rule scope.intros)
    fix pth t
    assume "path (c,is) t pth"
    
    assume "terminal_vertex t"
    hence "snd t = []" by auto

    from path_has_prefixes[OF `path (c,is) t pth` `snd t = []`, simplified, OF `prefixeq (is' @ [p']) is`]
    show "((c, is'), p') \<in> snd ` set pth".
  qed
  thus "v \<in> scope (v', p')" using `v =_` `v' = _` by simp
qed

sublocale Port_Graph nodes inPorts outPorts vertices nodeOf edges
proof
  show "nodeOf ` fset vertices \<subseteq> sset nodes"
    apply (auto simp add: fmember.rep_eq[symmetric] mem_vertices)
    apply (auto simp add: stream.set_map dest: iNodeOf_tree_at[OF iwf'_it])
    done
  next

  have "\<forall> e \<in> edges. valid_out_port (fst e) \<and> valid_in_port (snd e)"
    by (auto elim!: edges.cases simp add: edge_at_def
        dest: edge_from_valid_out_port edge_to_valid_in_port
        dest: hyp_edge_from_valid_out_port hyp_edge_to_valid_in_port)
    
  thus "\<forall>(ps1, ps2)\<in>edges. valid_out_port ps1 \<and> valid_in_port ps2" by auto
qed
  

sublocale Scoped_Graph nodes inPorts outPorts vertices nodeOf edges hyps..

lemma hyps_free_path_length:
  assumes "path v v' pth"
  assumes "hyps_free pth"
  shows "length pth + length (snd v') = length (snd v)"
using assms by induction (auto elim!: edge_step )

sublocale Instantiation inPorts outPorts nodeOf hyps fv ran_fv closed anyP nodes edges vertices labelsIn labelsOut pre_fv subst freshen inst..

sublocale Tasked_Proof_Graph freshen fv ran_fv closed anyP subst pre_fv antecedent consequent fresh_vars rules assumptions conclusions
  vertices nodeOf edges inst
proof
  fix v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2 p'
  assume assms: "((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) \<in> edges" "hyps (nodeOf v\<^sub>1) p\<^sub>1 = Some p'"
  from assms(1) hyps_correct[OF assms(2)]
  have "valid_out_port (v\<^sub>1, p\<^sub>1)" and "valid_in_port (v\<^sub>2, p\<^sub>2)" and "valid_in_port (v\<^sub>1, p')" and "v\<^sub>2 |\<in>| vertices"
    using valid_edges by auto

  from assms
  have "fst v\<^sub>1 = fst v\<^sub>2 \<and> prefixeq (snd v\<^sub>1@[p']) (snd v\<^sub>2)"
    by (cases v\<^sub>1; cases v\<^sub>2; auto elim!: edge_step)
  hence "scope' v\<^sub>1 p' v\<^sub>2"
    unfolding scope_valid_inport[OF `valid_in_port (v\<^sub>1, p')` `v\<^sub>2 |\<in>| vertices`].
  hence "v\<^sub>2 \<in> scope (v\<^sub>1, p')"
    unfolding in_scope[OF `valid_in_port (v\<^sub>1, p')`].
  thus "(v\<^sub>2, p\<^sub>2) = (v\<^sub>1, p') \<or> v\<^sub>2 \<in> scope (v\<^sub>1, p')" ..
  next

  fix v pth
  assume "path v v pth" and "hyps_free pth"
  from hyps_free_path_length[OF this]
  show "pth = []" by simp
  next

  fix v p
  assume "valid_in_port (v, p)"
  thus "\<exists>e\<in>edges. snd e = (v, p)"
  proof(induction v)
    fix c cis
    assume "valid_in_port ((c, cis), p)"
    hence "c \<in> set conclusions" by (auto simp add: mem_vertices)

    show "\<exists>e\<in>edges. snd e = ((c, cis), p)"
    proof(cases cis)
      case Nil
      with `valid_in_port ((c, cis), p)`
      have [simp]: "p = plain_ant c" by simp

      have "[] \<in> it_paths (it c)" by simp
      with `c \<in> set conclusions`
      have "edge_at c [] \<in> edges" by (rule regular_edge)
      moreover
      have "snd (edge_at c []) = ((c, []), plain_ant c)"
        by (simp add: edge_to_def)
      ultimately
      show ?thesis by (auto simp add: Nil simp del: snd_edge_at)
    next
      case (Cons c' "is")
      with `valid_in_port ((c, cis), p)`
      have [simp]: "c' = plain_ant c" and "is \<in> it_paths (it c)"
        and "p |\<in>| inPorts (iNodeOf (tree_at (it c) is))" by auto
      show ?thesis
      proof (cases "tree_at (it c) is")
        case INode
        hence "\<not> isHNode (tree_at (it c) is)" by simp
        from iwf'_it[OF `c \<in> set conclusions`] `is \<in> it_paths (it c)` this `p |\<in>| inPorts (iNodeOf (tree_at (it c) is))`
        have "is@[p] \<in> it_paths (it c)" by (rule it_path_SnocI)
        from `c \<in> set conclusions` this
        have "edge_at c (is@[p]) \<in> edges" by (rule regular_edge)
        moreover
        have "snd (edge_at c (is@[p])) = ((c, plain_ant c # is), p)"
          by (simp add: edge_to_def)
        ultimately
        show ?thesis by (auto simp add: Cons simp del: snd_edge_at)
      next
        case (HNode n s)
        from `c \<in> set conclusions` `is \<in> it_paths (it c)`  this
        have "hyp_edge_at c is n s \<in> edges"..
        moreover
        from HNode `p |\<in>| inPorts (iNodeOf (tree_at (it c) is))`
        have [simp]: "p = plain_ant anyP" by simp

        have "snd (hyp_edge_at c is n s) = ((c, plain_ant c # is), p)"
          by (simp add: hyp_edge_to_def)
        ultimately
        show ?thesis by (auto simp add: Cons simp del: snd_hyp_edge_at)
      qed
    qed
   qed
  next
  
  fix v 
  assume "v |\<in>| vertices"
  thus "\<exists>pth v'. path v v' pth \<and> terminal_vertex v'"
  proof(induct rule: vertices_induct)
    case (None c)
    hence "terminal_vertex (c,[])" by simp
    with path.intros(1)
    show ?case by blast
  next
    case (Some c "is")
    hence "path (c, plain_ant c # is) (c, []) (terminal_path_from c is)"
      by (rule path_terminal_path_from)
    moreover
    have "terminal_vertex (c,[])" using Some(1) by simp
    ultimately
    show ?case by blast
  qed
  next

  fix v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2
  assume "((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) \<in> edges"
  thus "labelAtOut v\<^sub>1 p\<^sub>1 = labelAtIn v\<^sub>2 p\<^sub>2"
  proof(cases)
    case (regular_edge c "is")
    show ?thesis
    proof(cases "is" rule:rev_cases)
      case Nil
      let "?t'" = "it c"
      have "labelAtOut v\<^sub>1 p\<^sub>1 = subst (iSubst ?t') (freshen (fidx vertices v\<^sub>1) (iOutPort ?t'))"
        using regular_edge Nil by (simp add: labelAtOut_def edge_at_def edge_from_def)
      also have "fidx vertices v\<^sub>1 = iAnnot ?t'" sorry
      also have "subst (iSubst ?t') (freshen (iAnnot ?t') (iOutPort ?t')) = snd (fst (tree.root (ts (to_form c))))"
        unfolding iwf'_subst_freshen_outPort[OF iwf'_it[OF `c \<in> set conclusions`]]..
      also have "\<dots> = to_form c" using `c \<in> set conclusions` by (simp add: ts_conc)
      also have "\<dots> = subst undefined (freshen (fidx vertices (c, [])) c)"
        using  `c \<in> set conclusions` by (simp add: closed_eq[OF conclusions_closed])
      also have "\<dots> = labelAtIn v\<^sub>2 p\<^sub>2"
        using regular_edge Nil by (simp add: labelAtIn_def edge_at_def)
      finally show ?thesis.
    next
      case (snoc is' i)
      let "?t1" = "tree_at (it c) (is'@[i])"
      let "?t2" = "tree_at (it c) is'"
      have "labelAtOut v\<^sub>1 p\<^sub>1 = subst (iSubst ?t1) (freshen (fidx vertices v\<^sub>1) (iOutPort ?t1))"
        using regular_edge snoc by (simp add: labelAtOut_def edge_at_def edge_from_def)
      also have "fidx vertices v\<^sub>1 = iAnnot ?t1" sorry
      also have "subst (iSubst ?t1) (freshen (iAnnot ?t1) (iOutPort ?t1)) = subst (iSubst ?t2) (freshen (iAnnot ?t2) (a_conc i))"
        by (rule iwf'_edge_match[OF iwf'_it[OF `c \<in> set conclusions`] `is \<in> it_paths (it c)`[unfolded snoc]])
      also have "iAnnot ?t2 = (fidx vertices (c, plain_ant c # is'))" sorry
      also have "subst (iSubst ?t2) (freshen (fidx vertices (c, plain_ant c # is')) (a_conc i)) = labelAtIn v\<^sub>2 p\<^sub>2"
        using regular_edge snoc by (simp add: labelAtIn_def edge_at_def)
      finally show ?thesis.
  qed
  next
    case (hyp_edge c "is" n s)
    let ?f = "subst s (freshen n anyP)"
    let ?h = "hyp_port_h_for (it c) is ?f"
    let ?his = "hyp_port_path_for (it c) is ?f"
    let "?t1" = "tree_at (it c) ?his"
    let "?t2" = "tree_at (it c) is"

    from `c \<in> set conclusions` `is \<in> it_paths (it c)` `tree_at (it c) is = HNode n s`
    have "?f \<in> hyps_along (it c) is"
      by (rule hyps_exist)

    have "labelAtOut v\<^sub>1 p\<^sub>1 = subst (iSubst ?t1) (freshen (fidx vertices v\<^sub>1) (labelsOut (iNodeOf ?t1) ?h))"
      using hyp_edge by (simp add: hyp_edge_at_def hyp_edge_from_def labelAtOut_def)
    also have "\<dots> = subst (iSubst ?t1) (freshen (iAnnot ?t1) (labelsOut (iNodeOf ?t1) ?h))"
      sorry
    also have "\<dots> = ?f" using `?f \<in> hyps_along (it c) is` by (rule local.hyp_port_eq[symmetric])
    also have "\<dots> = subst (iSubst ?t2) (freshen (iAnnot ?t2) anyP)"
      using hyp_edge by simp
    also have "iAnnot ?t2 = (fidx vertices (c, plain_ant c # is))" sorry
    also have "subst (iSubst ?t2) (freshen (fidx vertices (c, plain_ant c # is)) anyP) = labelAtIn v\<^sub>2 p\<^sub>2"
        using hyp_edge by (simp add: labelAtIn_def  hyp_edge_at_def hyp_edge_to_def)
    finally show ?thesis.
  qed
  next

  fix v p var v'
  assume "valid_in_port (v, p)"
  assume "var \<in> local_vars (nodeOf v) p"
  assume "freshenV (fidx vertices v) var \<in> ran_fv (inst v')"
  show "v' \<in> scope (v, p)"
    sorry
  next

  show "set (map Conclusion conclusions) \<subseteq> nodeOf ` fset vertices"
  proof-
  {
    fix c
    assume "c \<in> set conclusions"
    hence "(c, []) |\<in>| vertices" by simp
    hence "nodeOf (c, []) \<in> nodeOf ` fset vertices"
      unfolding fmember.rep_eq by (rule imageI)
    hence "Conclusion c \<in> nodeOf ` fset vertices"  by simp
  } thus ?thesis by auto
  qed
  
oops
    

end