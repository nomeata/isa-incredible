theory Incredible_Completeness
imports Natural_Deduction Incredible_Deduction Build_Incredible_Tree
begin

type_synonym 'form vertex = "('form \<times> nat list)"
type_synonym ('form, 'var) edge'' = "('form vertex, 'form, 'var) edge'"

locale Solved_Task =
  Abstract_Task  freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP antecedent consequent rules assumptions conclusions
   for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form"
    and antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list" 
    and consequent :: "'rule \<Rightarrow> 'form list" 
    and rules :: "'rule stream" 
    and assumptions :: "'form list" 
    and conclusions :: "'form list" +
  assumes solved: solved
begin

text {* Lets get our hand on concrete trees *}

definition ts :: "'form \<Rightarrow> (('form entailment) \<times> ('rule \<times> 'form) NatRule) tree" where
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

abbreviation it' where
  "it' c \<equiv> globalize [fidx conc_forms c, 0] (freshenLC v_away) (to_it (ts c))"

lemma local_iwf_it:
  assumes "c \<in> set conclusions"
  shows "local_iwf (it' c) (fst (root (ts c)))"
  using assms
    by (auto simp add: ts_conc conclusions_closed intro!: iwf_globalize' iwf_to_it ts_finite ts_wf)

definition vertices :: "'form vertex fset"  where
  "vertices = Abs_fset (Union ( set (map (\<lambda> c. insert (c, []) ((\<lambda> p. (c, 0 # p)) ` (it_paths (it' c))))  conclusions)))"

text {* For the remaining time, work with the tree with global freshness. *}

lemma mem_vertices: "v |\<in>| vertices \<longleftrightarrow>  (fst v \<in> set conclusions \<and> (snd v = [] \<or> snd v \<in> (op # 0) ` it_paths (it' (fst v))))"
  unfolding vertices_def fmember.rep_eq ffUnion.rep_eq 
  by (cases v)(auto simp add: Abs_fset_inverse Bex_def )

lemma prefixeq_vertices: "(c,is) |\<in>| vertices \<Longrightarrow> prefixeq is' is \<Longrightarrow> (c, is') |\<in>| vertices"
  by (cases is') (auto simp add: mem_vertices intro!: imageI elim: it_paths_prefixeq)

lemma none_vertices[simp]: "(c, []) |\<in>| vertices \<longleftrightarrow> c \<in> set conclusions"
  by (simp add: mem_vertices)

lemma some_vertices[simp]: "(c, i#is) |\<in>| vertices \<longleftrightarrow> c \<in> set conclusions \<and> i = 0 \<and> is \<in> it_paths (it' c)"
  by (auto simp add: mem_vertices)

lemma vertices_cases[consumes 1, case_names None Some]:
  assumes "v |\<in>| vertices"
  obtains c where "c \<in> set conclusions" and "v = (c, [])"
      |   c "is" where "c \<in> set conclusions" and "is \<in> it_paths (it' c)" and "v = (c, 0#is)"
using assms by (cases v; rename_tac "is"; case_tac "is"; auto)

lemma vertices_induct[consumes 1, case_names None Some]:
  assumes "v |\<in>| vertices"
  assumes "\<And> c. c \<in> set conclusions \<Longrightarrow> P (c, [])"
  assumes "\<And> c is . c \<in> set conclusions \<Longrightarrow> is \<in> it_paths (it' c) \<Longrightarrow> P (c, 0#is)"
  shows "P v"
using assms by (cases v; rename_tac "is"; case_tac "is"; auto)

lemma global_iwf_it:
  assumes "c \<in> set conclusions"
  shows "global_iwf (it' c) (fst (root (ts c)))"
  using assms
  sorry

text {* Start building the graph *}

fun nodeOf :: "'form vertex \<Rightarrow> ('form, 'rule) graph_node" where
  "nodeOf (pf, []) = Conclusion pf"
| "nodeOf (pf, i#is) = iNodeOf (tree_at (it' pf) is)"

fun inst where
  "inst (c,[]) = empty_subst"
 |"inst (c, i#is) = iSubst (tree_at (it' c) is)" 



lemma terminal_is_nil[simp]: "v |\<in>| vertices \<Longrightarrow> outPorts (nodeOf v) = {||} \<longleftrightarrow> snd v = []"
 apply (induction v rule: nodeOf.induct)
 apply auto
 apply (erule (1) iNodeOf_outPorts[rotated])
 apply (erule global_iwf_it)
 done


sublocale Vertex_Graph nodes inPorts outPorts vertices nodeOf.


definition edge_from :: "'form \<Rightarrow> nat list => ('form vertex \<times> ('form,'var) out_port)" where 
  "edge_from c is = ((c, 0 # is),  Reg (iOutPort (tree_at (it' c) is)))"

lemma fst_edge_from[simp]: "fst (edge_from c is) = (c, 0 # is)"
  by (simp add: edge_from_def)

fun in_port_at :: "('form \<times> nat list) \<Rightarrow> nat \<Rightarrow> ('form,'var) in_port" where
    "in_port_at (c, [])  _  = plain_ant c"
  | "in_port_at (c, _#is) i = inPorts' (iNodeOf (tree_at (it' c) is)) ! i"

definition edge_to :: "'form \<Rightarrow> nat list => ('form vertex \<times> ('form,'var) in_port)"  where
 "edge_to c is =
    (case rev is of   []   \<Rightarrow> ((c, []),           in_port_at (c, []) 0)
                    | i#is \<Rightarrow> ((c, 0 # (rev is)), in_port_at (c, (0#rev is)) i))"

lemma edge_to_Nil[simp]: "edge_to c [] = ((c, []), plain_ant c)"
  by (simp add: edge_to_def)

lemma edge_to_Snoc[simp]: "edge_to c (is@[i]) = ((c, 0 # is), in_port_at ((c, 0 # is)) i)"
  by (simp add: edge_to_def)

definition edge_at :: "'form \<Rightarrow> nat list => ('form, 'var) edge''"  where
   "edge_at c is = (edge_from c is, edge_to c is)"

lemma fst_edge_at[simp]: "fst (edge_at c is) = edge_from c is" by (simp add: edge_at_def)
lemma snd_edge_at[simp]: "snd (edge_at c is) = edge_to c is" by (simp add: edge_at_def)


lemma pre_hyps_exist:
  assumes "c \<in> set conclusions"
  assumes "is \<in> it_paths (it' c)"
  assumes "tree_at (it' c) is = (HNode i s)"
  shows "subst s (freshen i anyP) \<in> hyps_along (it' c) is"
proof-
  from assms(1)
  have "local_iwf (it' c) (fst (root (ts c)))" by (rule local_iwf_it)
  moreover
  note assms(2,3)
  moreover
  have "fst (fst (root (ts c))) |\<subseteq>| ass_forms"
    by (simp add: assms(1) ts_context)
  ultimately
  show ?thesis by (rule iwf_hyps_exist)
qed

lemma hyps_exist':
  assumes "c \<in> set conclusions"
  assumes "is \<in> it_paths (it' c)"
  assumes "tree_at (it' c) is = (HNode i s)"
  shows "subst s (freshen i anyP) \<in> hyps_along (it' c) is"
proof-
  from assms(1)
  have "global_iwf (it' c) (fst (root (ts c)))" by (rule global_iwf_it)
  moreover
  note assms(2,3)
  moreover
  have "fst (fst (root (ts c))) |\<subseteq>| ass_forms"
    by (simp add: assms(1) ts_context)
  ultimately
  show ?thesis by (rule iwf_hyps_exist)
qed



definition hyp_edge_to :: "'form \<Rightarrow> nat list => ('form vertex \<times> ('form,'var) in_port)" where
  "hyp_edge_to c is = ((c, 0 # is),  plain_ant anyP)"

(* TODO: Replace n and s by "subst s (freshen n anyP)" *)
definition hyp_edge_from :: "'form \<Rightarrow> nat list => nat \<Rightarrow> 'subst \<Rightarrow> ('form vertex \<times> ('form,'var) out_port)" where
  "hyp_edge_from c is n s = 
    ((c, 0 # hyp_port_path_for (it' c) is (subst s (freshen n anyP))),
     hyp_port_h_for (it' c) is (subst s (freshen n anyP)))"

definition hyp_edge_at  :: "'form \<Rightarrow> nat list => nat \<Rightarrow> 'subst \<Rightarrow> ('form, 'var) edge''" where
  "hyp_edge_at c is n s = (hyp_edge_from c is n s, hyp_edge_to c is)"

lemma fst_hyp_edge_at[simp]:
  "fst (hyp_edge_at c is n s) = hyp_edge_from c is n s" by (simp add:hyp_edge_at_def) 
lemma snd_hyp_edge_at[simp]:
  "snd (hyp_edge_at c is n s) = hyp_edge_to c is" by (simp add:hyp_edge_at_def)

inductive_set edges where
  regular_edge: "c \<in> set conclusions \<Longrightarrow> is \<in> it_paths (it' c) \<Longrightarrow> edge_at c is \<in> edges"
  | hyp_edge: "c \<in> set conclusions \<Longrightarrow> is \<in> it_paths (it' c) \<Longrightarrow> tree_at (it' c) is = HNode n s \<Longrightarrow> hyp_edge_at c is n s \<in> edges"

sublocale Pre_Port_Graph nodes inPorts outPorts vertices nodeOf edges.

lemma edge_from_valid_out_port:
  assumes "p \<in> it_paths (it' c)"
  assumes "c \<in> set conclusions"
  shows "valid_out_port (edge_from c p)"
using assms
by (auto simp add: edge_from_def intro: iwf_outPort global_iwf_it)

lemma edge_to_valid_in_port:
  assumes "p \<in> it_paths (it' c)"
  assumes "c \<in> set conclusions"
  shows "valid_in_port (edge_to c p)"
  using assms
  apply (auto simp add: edge_to_def inPorts_fset_of split: list.split elim!: it_paths_SnocE)
  apply (rule nth_mem)
  apply (drule (1) iwf_length_inPorts[OF global_iwf_it])
  apply auto
  done

lemma hyp_edge_from_valid_out_port:
  assumes "is \<in> it_paths (it' c)"
  assumes "c \<in> set conclusions"
  assumes "tree_at (it' c) is = HNode n s"
  shows "valid_out_port (hyp_edge_from c is n s)"
using assms
by(auto simp add: hyp_edge_from_def intro: hyp_port_outPort it_paths_prefix hyp_port_prefix  hyps_exist')

lemma hyp_edge_to_valid_in_port:
  assumes "is \<in> it_paths (it' c)"
  assumes "c \<in> set conclusions"
  assumes "tree_at (it' c) is = HNode n s"
  shows "valid_in_port (hyp_edge_to c is)"
using assms by (auto simp add: hyp_edge_to_def)



inductive scope' :: "'form vertex \<Rightarrow> ('form,'var) in_port \<Rightarrow> 'form \<times> nat list \<Rightarrow> bool" where
  "c \<in> set conclusions \<Longrightarrow>
   is' \<in> (op # 0) ` it_paths (it' c) \<Longrightarrow>
   prefixeq (is@[i]) is' \<Longrightarrow> 
   ip = in_port_at (c,is) i \<Longrightarrow>
   scope' (c, is) ip (c, is')"

inductive_simps scope_simp: "scope' v i v'"
inductive_cases scope_cases: "scope' v i v'"

lemma scope_valid:
  "scope' v i v' \<Longrightarrow> v' |\<in>| vertices"
by (auto elim: scope_cases)

lemma scope_valid_inport:
  "v' |\<in>| vertices \<Longrightarrow> scope' v ip  v' \<longleftrightarrow> (\<exists> i. fst v = fst v' \<and> prefixeq (snd v@[i]) (snd v') \<and> ip = in_port_at v i)"
by (cases v; cases v')  (auto simp add: scope'.simps mem_vertices)


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

definition terminal_path_from :: "'form \<Rightarrow> nat list => ('form, 'var) edge'' list" where
   "terminal_path_from c is = map (edge_at c) (rev (inits is))"

lemma terminal_path_from_Nil[simp]:
  "terminal_path_from c [] = [edge_at c []]"
  by (simp add: terminal_path_from_def)

lemma terminal_path_from_Snoc[simp]:
  "terminal_path_from c (is @ [i]) = edge_at  c (is@[i]) # terminal_path_from c is"
  by (simp add: terminal_path_from_def)

lemma path_terminal_path_from:
  "c \<in> set conclusions \<Longrightarrow>
  is \<in> it_paths (it' c) \<Longrightarrow>
  path (c, 0 # is) (c, []) (terminal_path_from c is)"
by (induction "is" rule: rev_induct)
   (auto simp add: path_cons_simp intro!: regular_edge elim: it_paths_SnocE)

lemma edge_step:
  assumes "(((a, b), ba), ((aa, bb), bc)) \<in> edges"
  obtains 
    i where "a = aa" and "b = bb@[i]" and "bc = in_port_at (aa,bb) i"  and "hyps (nodeOf (a, b)) ba = None"
  | i where "a = aa" and "prefixeq (b@[i]) bb" and "hyps (nodeOf (a, b)) ba = Some (in_port_at (a,b) i)"
using assms
proof(cases rule: edges.cases[consumes 1, case_names Reg Hyp])
  case (Reg c "is")
  then obtain i where  "a = aa" and "b = bb@[i]" and "bc = in_port_at (aa,bb) i"  and "hyps (nodeOf (a, b)) ba = None"
    by (auto elim!: edges.cases simp add: edge_at_def edge_from_def edge_to_def split: list.split list.split_asm)
  thus thesis by (rule that)
next
  case (Hyp c "is" n s)
  let ?i = "hyp_port_i_for (it' c) is (subst s (freshen n anyP))"
  from Hyp have "a = aa" and "prefixeq (b@[?i]) bb" and
    "hyps (nodeOf (a, b)) ba = Some (in_port_at (a,b) ?i)"
  by (auto simp add: edge_at_def edge_from_def edge_to_def hyp_edge_at_def hyp_edge_to_def hyp_edge_from_def
      intro: hyp_port_prefixeq hyps_exist' hyp_port_hyps)
  thus thesis by (rule that)
qed

lemma path_has_prefixes:
  assumes "path v v' pth"
  assumes "snd v' = []"
  assumes "prefixeq (is' @ [i]) (snd v)"
  shows "((fst v, is'), (in_port_at (fst v, is') i)) \<in> snd ` set pth"
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

    from `c \<in> set conclusions` `is \<in> it_paths (it' c)`
    have "path (c, 0#is) (c, []) (terminal_path_from c is)"
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
    show "scope' v' p' (c, 0#is)"
    proof(cases "is'" rule: rev_cases)
      case Nil
      with `(v',p') = edge_to c is'`
      have "v' = (c, [])" and "p' = plain_ant c"
        by (auto simp add: edge_to_def)
      with `c \<in> set conclusions` `is \<in> it_paths (it' c)`
      show ?thesis  by (auto intro!: scope'.intros)
    next
      case (snoc is'' i)
      with `(v',p') = edge_to c is'`
      have "v' = (c, 0 # is'')" and "p' = in_port_at v' i"
        by (auto simp add: edge_to_def)
      with `c \<in> set conclusions` `is \<in> it_paths (it' c)` `prefixeq is' is`[unfolded snoc]
      show ?thesis
        by (auto intro!: scope'.intros)
    qed
  qed
next
  assume "valid_in_port (v', p')"
  assume "scope' v' p' v"
  then obtain c is' i "is" where
    "v' = (c, is')" and "v = (c, is)" and "c \<in> set conclusions" and
    "p' = in_port_at v' i" and
    "is \<in> op # 0 ` it_paths (it' c)" and  "prefixeq (is' @ [i]) is"
    by (auto simp add: scope'.simps)

  from `scope' v' p' v`
  have "(c, is) |\<in>| vertices" unfolding `v = _` by (rule scope_valid)
  hence "(c, is) \<in> scope ((c, is'), p')"
  proof(rule scope.intros)
    fix pth t
    assume "path (c,is) t pth"
    
    assume "terminal_vertex t"
    hence "snd t = []" by auto

    from path_has_prefixes[OF `path (c,is) t pth` `snd t = []`, simplified, OF `prefixeq (is' @ [i]) is`]
    show "((c, is'), p') \<in> snd ` set pth" unfolding `p' = _ ` `v' = _ `.
  qed
  thus "v \<in> scope (v', p')" using `v =_` `v' = _` by simp
qed

sublocale Port_Graph nodes inPorts outPorts vertices nodeOf edges
proof
  show "nodeOf ` fset vertices \<subseteq> sset nodes"
    apply (auto simp add: fmember.rep_eq[symmetric] mem_vertices)
    apply (auto simp add: stream.set_map dest: iNodeOf_tree_at[OF global_iwf_it])
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

fun vidx :: "'form vertex \<Rightarrow> nat" where
   "vidx (c, [])   = isidx [fidx conc_forms c]"
  |"vidx (c, _#is) = iAnnot (tree_at (it' c) is)"

lemma vidx_inj: "inj_on vidx (fset vertices)"
  by(rule inj_onI)
    (auto simp add:  mem_vertices[unfolded fmember.rep_eq] iAnnot_globalize)

sublocale Instantiation inPorts outPorts nodeOf hyps  nodes edges vertices labelsIn labelsOut freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP vidx inst
proof
  show "inj_on vidx (fset vertices)" by (rule vidx_inj)
qed

sublocale  Well_Scoped_Graph nodes inPorts outPorts vertices nodeOf edges hyps
proof
  fix v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2 p'
  assume assms: "((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) \<in> edges" "hyps (nodeOf v\<^sub>1) p\<^sub>1 = Some p'"
  from assms(1) hyps_correct[OF assms(2)]
  have "valid_out_port (v\<^sub>1, p\<^sub>1)" and "valid_in_port (v\<^sub>2, p\<^sub>2)" and "valid_in_port (v\<^sub>1, p')" and "v\<^sub>2 |\<in>| vertices"
    using valid_edges by auto

  from assms
  have "\<exists> i. fst v\<^sub>1 = fst v\<^sub>2 \<and> prefixeq (snd v\<^sub>1@[i]) (snd v\<^sub>2) \<and> p' = in_port_at v\<^sub>1 i"
    by (cases v\<^sub>1; cases v\<^sub>2; auto elim!: edge_step)
  hence "scope' v\<^sub>1 p' v\<^sub>2"
    unfolding scope_valid_inport[OF `v\<^sub>2 |\<in>| vertices`].
  hence "v\<^sub>2 \<in> scope (v\<^sub>1, p')"
    unfolding in_scope[OF `valid_in_port (v\<^sub>1, p')`].
  thus "(v\<^sub>2, p\<^sub>2) = (v\<^sub>1, p') \<or> v\<^sub>2 \<in> scope (v\<^sub>1, p')" ..
qed

sublocale Acyclic_Graph nodes inPorts outPorts vertices nodeOf edges hyps 
proof
  fix v pth
  assume "path v v pth" and "hyps_free pth"
  from hyps_free_path_length[OF this]
  show "pth = []" by simp
qed

sublocale Saturated_Graph nodes inPorts outPorts vertices nodeOf edges
proof
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

      have "[] \<in> it_paths (it' c)" by simp
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
      have [simp]: "c' = 0" and "is \<in> it_paths (it' c)"
        and "p |\<in>| inPorts (iNodeOf (tree_at (it' c) is))" by auto
       
      from this(3) obtain i where
        "i < length (inPorts' (iNodeOf (tree_at (it' c) is)))" and
        "p = inPorts' (iNodeOf (tree_at (it' c) is)) ! i"
          by (auto simp add: inPorts_fset_of in_set_conv_nth)

      show ?thesis
      proof (cases "tree_at (it' c) is")
        case INode
        hence "\<not> isHNode (tree_at (it' c) is)" by simp
        from iwf_length_inPorts_not_HNode[OF global_iwf_it[OF `c \<in> set conclusions`]  `is \<in> it_paths (it' c)` this]
             `i < length (inPorts' (iNodeOf (tree_at (it' c) is)))`
        have "i < length (iAnts (tree_at (it' c) is))" by simp
        with `is \<in> it_paths (it' c)`
        have "is@[i] \<in> it_paths (it' c)" by (rule it_path_SnocI)
        from `c \<in> set conclusions` this
        have "edge_at c (is@[i]) \<in> edges" by (rule regular_edge)
        moreover
        have "snd (edge_at c (is@[i])) = ((c, 0 # is),  inPorts' (iNodeOf (tree_at (it' c) is)) ! i)"
          by (simp add: edge_to_def)
        ultimately
        show ?thesis by (auto simp add: Cons `p = _` simp del: snd_edge_at)
      next
        case (HNode n s)
        from `c \<in> set conclusions` `is \<in> it_paths (it' c)`  this
        have "hyp_edge_at c is n s \<in> edges"..
        moreover
        from HNode `p |\<in>| inPorts (iNodeOf (tree_at (it' c) is))`
        have [simp]: "p = plain_ant anyP" by simp

        have "snd (hyp_edge_at c is n s) = ((c, 0 # is), p)"
          by (simp add: hyp_edge_to_def)
        ultimately
        show ?thesis by (auto simp add: Cons simp del: snd_hyp_edge_at)
      qed
    qed
   qed
qed

sublocale Pruned_Port_Graph nodes inPorts outPorts vertices nodeOf edges
proof
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
    hence "path (c, 0 # is) (c, []) (terminal_path_from c is)"
      by (rule path_terminal_path_from)
    moreover
    have "terminal_vertex (c,[])" using Some(1) by simp
    ultimately
    show ?case by blast
  qed
qed

sublocale Well_Shaped_Graph  nodes inPorts outPorts vertices nodeOf edges hyps..

sublocale Solution inPorts outPorts nodeOf hyps nodes vertices  labelsIn labelsOut freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP vidx inst edges
proof
  fix v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2
  assume "((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) \<in> edges"
  thus "labelAtOut v\<^sub>1 p\<^sub>1 = labelAtIn v\<^sub>2 p\<^sub>2"
  proof(cases rule:edges.cases)
    case (regular_edge c "is")
   
    from `((v\<^sub>1, p\<^sub>1), v\<^sub>2, p\<^sub>2) = edge_at c is`
    have "(v\<^sub>1,p\<^sub>1) = edge_from c is" using fst_edge_at by (metis fst_conv)
    hence [simp]: "v\<^sub>1 = (c, 0 # is)" by (simp add: edge_from_def)

    show ?thesis
    proof(cases "is" rule:rev_cases)
      case Nil
      let "?t'" = "it' c"
      have "labelAtOut v\<^sub>1 p\<^sub>1 = subst (iSubst ?t') (freshen (vidx v\<^sub>1) (iOutPort ?t'))"
        using regular_edge Nil by (simp add: labelAtOut_def edge_at_def edge_from_def)
      also have "vidx v\<^sub>1 = iAnnot ?t'" by (simp add:  Nil)
      also have "subst (iSubst ?t') (freshen (iAnnot ?t') (iOutPort ?t')) = snd (fst (root (ts c)))"
        unfolding iwf_subst_freshen_outPort[OF global_iwf_it[OF `c \<in> set conclusions`]]..
      also have "\<dots> = c" using `c \<in> set conclusions` by (simp add: ts_conc)
      also have "\<dots> = labelAtIn v\<^sub>2 p\<^sub>2"
        using  `c \<in> set conclusions`  regular_edge Nil
        by (simp add: labelAtIn_def edge_at_def freshen_closed conclusions_closed closed_no_lconsts)
      finally show ?thesis.
    next
      case (snoc is' i)
      let "?t1" = "tree_at (it' c) (is'@[i])"
      let "?t2" = "tree_at (it' c) is'"
      have "labelAtOut v\<^sub>1 p\<^sub>1 = subst (iSubst ?t1) (freshen (vidx v\<^sub>1) (iOutPort ?t1))"
        using regular_edge snoc by (simp add: labelAtOut_def edge_at_def edge_from_def)
      also have "vidx v\<^sub>1 = iAnnot ?t1" using snoc regular_edge(3) by simp
      also have "subst (iSubst ?t1) (freshen (iAnnot ?t1) (iOutPort ?t1))
          = subst (iSubst ?t2) (freshen (iAnnot ?t2) (a_conc (inPorts' (iNodeOf ?t2) ! i)))"
        by (rule iwf_edge_match[OF global_iwf_it[OF `c \<in> set conclusions`] `is \<in> it_paths (it' c)`[unfolded snoc]])
      also have "iAnnot ?t2 = vidx (c, 0 # is')" by simp
      also have "subst (iSubst ?t2) (freshen (vidx (c, 0 # is')) (a_conc (inPorts' (iNodeOf ?t2) ! i))) = labelAtIn v\<^sub>2 p\<^sub>2"
        using regular_edge snoc by (simp add: labelAtIn_def edge_at_def)
      finally show ?thesis.
  qed
  next
    case (hyp_edge c "is" n s)
    let ?f = "subst s (freshen n anyP)"
    let ?h = "hyp_port_h_for (it' c) is ?f"
    let ?his = "hyp_port_path_for (it' c) is ?f"
    let "?t1" = "tree_at (it' c) ?his"
    let "?t2" = "tree_at (it' c) is"

    from `c \<in> set conclusions` `is \<in> it_paths (it' c)` `tree_at (it' c) is = HNode n s`
    have "?f \<in> hyps_along (it' c) is"
      by (rule hyps_exist')

    from `((v\<^sub>1, p\<^sub>1), v\<^sub>2, p\<^sub>2) = hyp_edge_at c is n s`
    have "(v\<^sub>1,p\<^sub>1) = hyp_edge_from c is n s" using fst_hyp_edge_at by (metis fst_conv)
    hence [simp]: "v\<^sub>1 = (c, 0 # ?his)" by (simp add: hyp_edge_from_def)


    have "labelAtOut v\<^sub>1 p\<^sub>1 = subst (iSubst ?t1) (freshen (vidx v\<^sub>1) (labelsOut (iNodeOf ?t1) ?h))"
      using hyp_edge by (simp add: hyp_edge_at_def hyp_edge_from_def labelAtOut_def)
    also have "vidx v\<^sub>1 = iAnnot ?t1" by simp
    also have "subst (iSubst ?t1) (freshen (iAnnot ?t1) (labelsOut (iNodeOf ?t1) ?h)) = ?f" using `?f \<in> hyps_along (it' c) is` by (rule local.hyp_port_eq[symmetric])
    also have "\<dots> = subst (iSubst ?t2) (freshen (iAnnot ?t2) anyP)"  using hyp_edge by simp
    also have "subst (iSubst ?t2) (freshen (iAnnot ?t2) anyP) = labelAtIn v\<^sub>2 p\<^sub>2"
        using hyp_edge by (simp add: labelAtIn_def  hyp_edge_at_def hyp_edge_to_def)
    finally show ?thesis.
  qed
qed

sublocale Well_Scoped_Instantiation  freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP inPorts outPorts nodeOf hyps  nodes vertices labelsIn labelsOut vidx inst edges local_vars
proof
  fix v p var v'
  assume "valid_in_port (v, p)"
  then obtain c "is" where "v = (c,is)" by (cases v, auto)

  from `valid_in_port (v, p)` `v= _`
  have "(c,is) |\<in>| vertices"  and "p |\<in>| inPorts (nodeOf (c, is))" by simp_all
  hence "c \<in> set conclusions" by (simp add: mem_vertices)
  
  from `p |\<in>| _` obtain i where
    "i < length (inPorts' (nodeOf (c, is)))" and
    "p = inPorts' (nodeOf (c, is)) ! i" by (auto simp add: inPorts_fset_of in_set_conv_nth)
  hence "p = in_port_at (c, is) i" by (cases "is") auto

  assume "v' |\<in>| vertices"
  then obtain c' is' where "v' = (c',is')" by (cases v', auto)

  assume "var \<in> local_vars (nodeOf v) p"
  hence "var \<in> a_fresh p" by simp

  thm iwf_local_not_in_subst[OF local_iwf_it[OF `c \<in> set conclusions`]]

  hence fresh_not_self: "freshenLC (vidx v) var \<notin> subst_lconsts (inst v)"
  proof(cases "is")
    case Nil thus ?thesis by (simp add: `v=_`)
  next
    case (Cons i is'')

    from `valid_in_port (v, p)` `v= _` Cons
    have  "i=0" "is'' \<in> it_paths (it' c)" by auto

    from  `p |\<in>| inPorts (nodeOf (c, is))`
    have "p |\<in>| inPorts (iNodeOf (tree_at (it' c) is''))"
      by (simp add:  `v= _` Cons)

    from iwf_local_not_in_subst[OF
        local_iwf_it[OF `c \<in> set conclusions`]
        `is'' \<in> it_paths (it' c)`
        `p |\<in>| inPorts (iNodeOf (tree_at (it' c) is''))`
        `var \<in> a_fresh p`
        ]
    show ?thesis by (simp add: `v= _` Cons)
  qed
  
  assume "freshenLC (vidx v) var \<in> subst_lconsts (inst v')"
  also have "subst_lconsts (inst v') \<subseteq> Union ((\<lambda> is''. range (freshenLC (vidx (c', is'')))) ` set (inits is'))"
    sorry
  finally obtain is'' where "prefixeq is'' is'"  and "vidx (c,is) = vidx (c', is'')"
    by (auto simp add: `v=_`)

  from `prefixeq is'' is'` `v' |\<in>| vertices` `v' = _`
  have "(c',is'') |\<in>| vertices" using prefixeq_vertices by metis

  from `(c',is'') |\<in>| vertices` `(c,is) |\<in>| vertices` `vidx (c,is) = vidx (c', is'')`
  have "c' = c" and "is'' = is"  by (auto dest: Fun.inj_onD[OF vidx_inj] simp add: fmember.rep_eq)

  from `freshenLC (vidx v) var \<in> subst_lconsts (inst v')`
       `freshenLC (vidx v) var \<notin> subst_lconsts (inst v)`
  have "v \<noteq> v'" by auto
  hence "is' \<noteq> is''" by (simp add: `is'' = is` `c' = c` `v = _` `v' = _`)
  with `prefixeq is'' is'` `is'' = is`
  have "prefix is is'" by simp
    

  have "prefixeq (is @ [i]) is'" sorry

  from `prefixeq (is @ [i]) is'`
  have "is' \<noteq> []" by (cases is') auto
  with `v' |\<in>| vertices` `v' = _`
  obtain is'' where
    "is' = 0 # is''"  and "is'' \<in> it_paths (it' c')"
      by (auto elim: vertices_cases)
 
  from `c \<in> set conclusions`  `is'' \<in> it_paths (it' c')` `prefixeq (is @ [i]) is'` `p = in_port_at (c, is) i`
  have "scope' v p v'"
  unfolding `v=_` `v'=_` `c' = _` `is' = _`  by (auto intro: scope'.intros)
  thus "v' \<in> scope (v, p)" using `valid_in_port (v, p)` by (simp add: in_scope)
qed

sublocale Scoped_Proof_Graph freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP  inPorts outPorts nodeOf hyps nodes vertices labelsIn labelsOut vidx inst edges local_vars..
   
sublocale Tasked_Proof_Graph freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP antecedent consequent fresh_vars rules assumptions conclusions
  vertices nodeOf edges vidx inst
proof
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
qed  

end

end