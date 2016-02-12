theory Incredible_Deduction
imports
  Main 
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Stream"
  Abstract_Formula
begin

locale Port_Graph_Signature =
  fixes nodes :: "'node stream"
  fixes inPorts :: "'node \<Rightarrow> 'inPort fset"
  fixes outPorts :: "'node \<Rightarrow> 'outPort fset"

type_synonym ('v, 'outPort, 'inPort) edge = "(('v \<times> 'outPort) \<times> ('v \<times> 'inPort))"

locale Pre_Port_Graph =
  Port_Graph_Signature
  _ inPorts outPorts for inPorts :: "'node \<Rightarrow> 'inPort fset" and outPorts :: "'node \<Rightarrow> 'outPort fset"  +
  fixes vertices :: "'v fset"
  fixes nodeOf :: "'v \<Rightarrow> 'node"
  fixes edges :: "('v, 'outPort, 'inPort) edge set"
begin
  fun valid_out_port where "valid_out_port (v,p) \<longleftrightarrow> v |\<in>| vertices \<and> p |\<in>| outPorts (nodeOf v)"
  fun valid_in_port  where "valid_in_port (v,p) \<longleftrightarrow> v |\<in>| vertices \<and> p |\<in>| inPorts (nodeOf v)" 

  fun edge_begin :: "(('v \<times> 'outPort) \<times> ('v \<times> 'inPort)) \<Rightarrow> 'v" where
    "edge_begin ((v1,p1),(v2,p2)) = v1"
  fun edge_end :: "(('v \<times> 'outPort) \<times> ('v \<times> 'inPort)) \<Rightarrow> 'v" where
    "edge_end ((v1,p1),(v2,p2)) = v2"

  lemma edge_begin_tup: "edge_begin x = fst (fst x)" by (metis edge_begin.simps prod.collapse)
  lemma edge_end_tup: "edge_end x = fst (snd x)" by (metis edge_end.simps prod.collapse)

  inductive path :: "'v \<Rightarrow> 'v \<Rightarrow> ('v, 'outPort, 'inPort) edge list \<Rightarrow> bool"   where
    path_empty: "path v v []" |
    path_cons: "e \<in> edges \<Longrightarrow> path (edge_end e) v' pth \<Longrightarrow> path (edge_begin e) v' (e#pth)"

  inductive_simps path_cons_simp': "path v v' (e#pth)"
  inductive_simps path_empty_simp[simp]: "path v v' []"
  lemma path_cons_simp: "path v v' (e # pth) \<longleftrightarrow> fst (fst e) = v \<and> e \<in> edges \<and> path (fst (snd e)) v' pth"
    by(auto simp add: path_cons_simp', metis prod.collapse)

  lemma path_appendI: "path v v' pth1 \<Longrightarrow> path v' v'' pth2 \<Longrightarrow> path v v'' (pth1@pth2)"
    by (induction pth1 arbitrary: v) (auto simp add: path_cons_simp )

  lemma path_split: "path v v' (pth1@[e]@pth2) \<longleftrightarrow> path v (edge_end e) (pth1@[e]) \<and> path (edge_end e) v' pth2"
    by (induction pth1 arbitrary: v) (auto simp add: path_cons_simp edge_end_tup intro: path_empty)

  lemma path_split2: "path v v' (pth1@(e#pth2)) \<longleftrightarrow> path v (edge_begin e) pth1 \<and> path (edge_begin e) v' (e#pth2)"
    by (induction pth1 arbitrary: v) (auto simp add: path_cons_simp edge_begin_tup intro: path_empty)

  lemma path_snoc: "path v v' (pth1@[e]) \<longleftrightarrow> e \<in> edges \<and> path v (edge_begin e) pth1 \<and> edge_end e = v'"
    by (auto simp add: path_split2 path_cons_simp edge_end_tup edge_begin_tup)



  fun terminal_node where
    "terminal_node n \<longleftrightarrow> outPorts n = {||}"
  fun terminal_vertex where
    "terminal_vertex v \<longleftrightarrow> terminal_node (nodeOf v)"

  inductive_set scope for ps where
    "v |\<in>| vertices \<Longrightarrow> (\<And> pth v'.  path v v' pth \<Longrightarrow> terminal_vertex v' \<Longrightarrow> ps \<in> snd ` set pth)
    \<Longrightarrow> v \<in> scope ps"

  lemma scope_find:
    assumes "v \<in> scope ps"
    assumes "terminal_vertex v'"
    assumes "path v v' pth"
    shows "ps \<in> snd ` set pth"
  using assms by (auto simp add: scope.simps)

  lemma snd_set_split:
    assumes "ps \<in> snd ` set pth"
    obtains pth1 pth2 e  where "pth = pth1@[e]@pth2" and "snd e = ps" and "ps \<notin> snd ` set pth1"
    using assms
    proof (atomize_elim, induction pth)
      case Nil thus ?case by simp
    next
      case (Cons e pth)
      show ?case
      proof(cases "snd e = ps")
        case True
        hence "e # pth = [] @ [e] @ pth \<and> snd e = ps \<and> ps \<notin> snd ` set []" by auto
        thus ?thesis by (intro exI)
      next
        case False
        with Cons(2)
        have "ps \<in> snd ` set pth" by auto
        from Cons.IH[OF this this] 
        obtain pth1 e' pth2 where "pth = pth1 @ [e'] @ pth2 \<and> snd e' = ps \<and> ps \<notin> snd ` set pth1" by auto
        with False
        have "e#pth = (e# pth1) @ [e'] @ pth2 \<and> snd e' = ps \<and> ps \<notin> snd ` set (e#pth1)" by auto
        thus ?thesis by blast
      qed
    qed

  lemma scope_split:
    assumes "v \<in> scope ps"
    assumes "path v v' pth"
    assumes "terminal_vertex v'"
    obtains pth1 e pth2
    where "pth = (pth1@[e])@pth2" and "path v (fst ps) (pth1@[e])" and "path (fst ps) v' pth2" and "snd e = ps" and "ps \<notin> snd ` set pth1"
  proof-
    from assms
    have "ps \<in> snd ` set pth" by (auto simp add: scope.simps)
    then obtain pth1 pth2 e  where "pth = pth1@[e]@pth2" and "snd e = ps" and "ps \<notin> snd ` set pth1" by (rule snd_set_split)
    
    from `path _ _ _` and `pth = pth1@[e]@pth2`
    have "path v (edge_end e) (pth1@[e])" and "path (edge_end e) v' pth2" by (metis path_split)+
    show thesis
    proof(rule that)
      show "pth = (pth1@[e])@pth2" using `pth= _` by simp
      show "path v (fst ps) (pth1@[e])" using `path v (edge_end e) (pth1@[e])`  `snd e = ps` by (simp add: edge_end_tup)
      show "path (fst ps) v' pth2" using `path (edge_end e) v' pth2`  `snd e = ps` by (simp add: edge_end_tup)
      show "ps \<notin> snd ` set pth1" by fact
      show "snd e = ps" by fact
    qed
  qed
  
end

locale Port_Graph = Pre_Port_Graph +
  assumes valid_nodes: "nodeOf ` fset vertices  \<subseteq> sset nodes"
  assumes valid_edges: "\<forall> (ps1,ps2) \<in> edges. valid_out_port ps1 \<and> valid_in_port ps2"

locale Pruned_Port_Graph = Port_Graph +
  assumes pruned: "\<And>v.  v |\<in>| vertices \<Longrightarrow> (\<exists>pth v'. path v v' pth \<and> terminal_vertex v')"
begin
  lemma scopes_not_refl:
    assumes "v |\<in>| vertices"
    shows "v \<notin> scope (v,p)"
  proof(rule notI)
    assume "v \<in> scope (v,p)"

    from pruned[OF assms]
    obtain pth t where "terminal_vertex t" and "path v t pth" and least: "\<forall> pth'. path v t pth' \<longrightarrow> length pth \<le> length pth'"
      by atomize_elim (auto simp del: terminal_vertex.simps elim: ex_has_least_nat)
        
    from scope_split[OF `v \<in> scope (v,p)` `path v t pth` `terminal_vertex t`]
    obtain pth1 e pth2 where "pth = (pth1 @ [e]) @ pth2" "path v t pth2" by (metis fst_conv)

    from this(2) least
    have "length pth \<le> length pth2" by auto
    with `pth = _`
    show False by auto
  qed

  lemma scopes_nest:
    fixes ps1 ps2
    (* assumes "valid_in_port ps1" and "valid_in_port ps2" not needed *)
    shows "scope ps1 \<subseteq> scope ps2 \<or> scope ps2 \<subseteq> scope ps1 \<or> scope ps1 \<inter> scope ps2 = {}"
  proof(cases "ps1 = ps2")
    assume "ps1 \<noteq> ps2"
    {
    fix v
    assume "v \<in> scope ps1 \<inter> scope ps2"
    hence "v |\<in>| vertices" using scope.simps by auto
    then obtain pth t where "path v t pth" and "terminal_vertex t" using pruned by blast
  
    from `path v t pth` and `terminal_vertex t` and `v \<in> scope ps1 \<inter> scope ps2`
    obtain pth1a e1 pth1b  where "pth = (pth1a@[e1])@pth1b" and "path v (fst ps1) (pth1a@[e1])" and "snd e1 = ps1" and "ps1 \<notin> snd ` set pth1a"
      by (auto elim: scope_split)
  
    from `path v t pth` and `terminal_vertex t` and `v \<in> scope ps1 \<inter> scope ps2`
    obtain pth2a e2 pth2b  where "pth = (pth2a@[e2])@pth2b" and "path v (fst ps2) (pth2a@[e2])" and "snd e2 = ps2" and "ps2 \<notin> snd ` set pth2a"
      by (auto elim: scope_split)
   
    from `pth = (pth1a@[e1])@pth1b` `pth = (pth2a@[e2])@pth2b`
    have "set pth1a \<subseteq> set pth2a \<or> set pth2a \<subseteq> set pth1a" by (auto simp add: append_eq_append_conv2)
    hence "scope ps1 \<subseteq> scope ps2 \<or> scope ps2 \<subseteq> scope ps1"
    proof
      assume "set pth1a \<subseteq> set pth2a" with `ps2 \<notin> _`
      have "ps2 \<notin> snd ` set (pth1a@[e1])" using `ps1 \<noteq> ps2` `snd e1 = ps1` by auto
  
      have "scope ps1 \<subseteq> scope ps2"
      proof
        fix v'
        assume "v' \<in> scope ps1"
        hence "v' |\<in>| vertices" using scope.simps by auto
        thus "v' \<in> scope ps2"
        proof(rule scope.intros)
          fix pth' t'
          assume "path v' t' pth'" and "terminal_vertex t'"
          with `v' \<in> scope ps1`
          obtain pth3a e3 pth3b where "pth' = (pth3a@[e3])@pth3b" and "path (fst ps1) t' pth3b"
            by (auto elim: scope_split)
  
          have "path v t' ((pth1a@[e1]) @ pth3b)" using `path v (fst ps1) (pth1a@[e1])` and `path (fst ps1) t' pth3b`
            by (rule path_appendI)
          with `terminal_vertex t'` `v \<in> _`
          have "ps2 \<in> snd ` set ((pth1a@[e1]) @ pth3b)" by (meson IntD2 scope.cases)
          hence "ps2 \<in> snd ` set pth3b" using `ps2 \<notin> snd \` set (pth1a@[e1])` by auto
          thus "ps2 \<in> snd ` set pth'" using `pth'=_` by auto
        qed
      qed
      thus ?thesis by simp
    next
      assume "set pth2a \<subseteq> set pth1a" with `ps1 \<notin> _`
      have "ps1 \<notin> snd ` set (pth2a@[e2])" using `ps1 \<noteq> ps2` `snd e2 = ps2` by auto
  
      have "scope ps2 \<subseteq> scope ps1"
      proof
        fix v'
        assume "v' \<in> scope ps2"
        hence "v' |\<in>| vertices" using scope.simps by auto
        thus "v' \<in> scope ps1"
        proof(rule scope.intros)
          fix pth' t'
          assume "path v' t' pth'" and "terminal_vertex t'"
          with `v' \<in> scope ps2`
          obtain pth3a e3 pth3b where "pth' = (pth3a@[e3])@pth3b" and "path (fst ps2) t' pth3b" 
            by (auto elim: scope_split)
  
          have "path v t' ((pth2a@[e2]) @ pth3b)" using `path v (fst ps2) (pth2a@[e2])` and `path (fst ps2) t' pth3b`
            by (rule path_appendI)
          with `terminal_vertex t'` `v \<in> _`
          have "ps1 \<in> snd ` set ((pth2a@[e2]) @ pth3b)" by (meson IntD1 scope.cases)
          hence "ps1 \<in> snd ` set pth3b" using `ps1 \<notin> snd \` set (pth2a@[e2])` by auto
          thus "ps1 \<in> snd ` set pth'" using `pth'=_` by auto
        qed
      qed
      thus ?thesis by simp
    qed
    }
    thus ?thesis by blast
  qed simp
end


locale Port_Graph_Signature_Scoped =
  Port_Graph_Signature +
  fixes hyps :: "'node \<Rightarrow> 'outPort \<rightharpoonup> 'inPort"
  assumes hyps_correct: "hyps n p1 = Some p2 \<Longrightarrow> p1 |\<in>| outPorts n \<and> p2 |\<in>| inPorts n"
begin
  inductive_set hyps_for' :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'outPort set" for n p
    where "hyps n h = Some p \<Longrightarrow> h \<in> hyps_for' n p"

  lemma hyps_for'_subset: "hyps_for' n p \<subseteq> fset (outPorts n)"
    using hyps_correct by (meson hyps_for'.cases notin_fset subsetI)
 
  context includes fset.lifting
  begin
  lift_definition hyps_for  :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'outPort fset" is hyps_for'
    by (meson finite_fset hyps_for'_subset rev_finite_subset)
  lemma hyps_for_simp[simp]: "h |\<in>| hyps_for n p \<longleftrightarrow> hyps n h = Some p"
    by transfer (simp add: hyps_for'.simps)
  lemma hyps_for_simp'[simp]: "h \<in> fset (hyps_for n p) \<longleftrightarrow> hyps n h = Some p"
    by transfer (simp add: hyps_for'.simps)
  end
  lemma hyps_for_subset: "hyps_for n p |\<subseteq>| outPorts n"
    using hyps_for'_subset
    by (fastforce simp add: fmember.rep_eq hyps_for.rep_eq simp del: hyps_for_simp hyps_for_simp')
 
end

locale Scoped_Graph = Port_Graph + Port_Graph_Signature_Scoped

locale Well_Scoped_Graph = Scoped_Graph +
  assumes well_scoped: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = Some p' \<Longrightarrow> (v\<^sub>2,p\<^sub>2) = (v\<^sub>1,p') \<or> v\<^sub>2 \<in> scope (v\<^sub>1,p')"

locale Acyclic_Graph = Scoped_Graph +
  assumes acyclic: "path v v pth \<Longrightarrow> pth = [] \<or> (\<exists> v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2. ((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> set pth \<and> hyps (nodeOf v\<^sub>1) p\<^sub>1 \<noteq> None)"

context Acyclic_Graph
begin

definition hyps_free where
  "hyps_free pth = (\<forall> v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2. ((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> set pth \<longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = None)"

lemma hyps_free_Nil[simp]: "hyps_free []" by (simp add: hyps_free_def)

lemma hyps_free_Cons[simp]: "hyps_free (e#pth) \<longleftrightarrow> hyps_free pth \<and> hyps (nodeOf (fst (fst e))) (snd (fst e)) = None"
  by (auto simp add: hyps_free_def) (metis prod.collapse)


lemma hyps_free_acyclic: "path v v pth \<Longrightarrow> hyps_free pth \<Longrightarrow> pth = []"
  by (drule acyclic) (fastforce simp add: hyps_free_def)

lemma path_vertices_shift:
  assumes "path v v' pth"
  shows "map fst (map fst pth)@[v'] = v#map fst (map snd pth)"
using assms by induction auto

inductive terminal_path where
    terminal_path_empty: "terminal_vertex v \<Longrightarrow> terminal_path v v []" |
    terminal_path_cons: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> terminal_path v\<^sub>2 v' pth \<Longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = None \<Longrightarrow> terminal_path v\<^sub>1 v' (((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2))#pth)"

lemma terminal_path_is_path:
  assumes "terminal_path v v' pth"
  shows "path v v' pth"
using assms by induction (auto simp add: path_cons_simp)

lemma terminal_path_is_hyps_free:
  assumes "terminal_path v v' pth"
  shows "hyps_free pth"
using assms
  by induction (auto simp add: hyps_free_def)

lemma terminal_path_end_is_terminal:
  assumes "terminal_path v v' pth"
  shows "terminal_vertex v'"
using assms by induction

lemma terminal_pathI:
  assumes "path v v' pth"
  assumes "hyps_free pth"
  assumes "terminal_vertex v'"
  shows "terminal_path v v' pth"
using assms
by induction (auto intro: terminal_path.intros)


lemma hyps_free_vertices_distinct:
  assumes "terminal_path v v' pth"
  shows "distinct (map fst (map fst pth)@[v'])"
using assms
proof(induction v v' pth)
  case terminal_path_empty
  show ?case by simp
next
  case (terminal_path_cons v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2 v' pth)
  note terminal_path_cons.IH
  moreover
  have "v\<^sub>1 \<notin> fst ` fst ` set pth"
  proof
    assume "v\<^sub>1 \<in> fst ` fst ` set pth"
    then obtain pth1 e' pth2 where "pth = pth1@[e']@pth2" and "v\<^sub>1 = fst (fst e')"
      apply (atomize_elim)
      apply (induction pth)
      apply simp
      apply (auto)
      apply (rule exI[where x = "[]"])
      apply simp
      by (metis Cons_eq_appendI image_eqI prod.sel(1))
    with terminal_path_is_path[OF `terminal_path v\<^sub>2 v' pth`]
    have "path v\<^sub>2 v\<^sub>1 pth1" by (simp add:  path_split2 edge_begin_tup)
    with `((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) \<in> _`
    have "path v\<^sub>1 v\<^sub>1 (((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) # pth1)" by (simp add: path_cons_simp)
    moreover
    from terminal_path_is_hyps_free[OF `terminal_path v\<^sub>2 v' pth`]
         `hyps (nodeOf v\<^sub>1) p\<^sub>1 = None`
         `pth = pth1@[e']@pth2`
    have "hyps_free(((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) # pth1)"
      by (auto simp add: hyps_free_def)
    ultimately
    show False  using hyps_free_acyclic by blast
  qed
  moreover
  have "v\<^sub>1 \<noteq> v'"
    using hyps_free_acyclic path_cons terminal_path_cons.hyps(1) terminal_path_cons.hyps(2) terminal_path_cons.hyps(3) terminal_path_is_hyps_free terminal_path_is_path by fastforce
  ultimately
  show ?case by (auto simp add: comp_def)
qed

lemma hyps_free_vertices_distinct':
  assumes "terminal_path v v' pth"
  shows "distinct (v # map fst (map snd pth))"
  using hyps_free_vertices_distinct[OF assms]
  unfolding path_vertices_shift[OF terminal_path_is_path[OF assms]]
  .

lemma hyps_free_limited:
  assumes "terminal_path v v' pth"
  shows "length pth \<le> fcard vertices"
proof-
  have "length pth = length (map fst (map fst pth))" by simp
  also
  from hyps_free_vertices_distinct[OF assms]
  have "distinct (map fst (map fst pth))" by simp
  hence "length (map fst (map fst pth)) = card (set (map fst (map fst pth)))"
    by (rule distinct_card[symmetric])
  also have "\<dots> \<le> card (fset vertices)"
  proof (rule card_mono[OF finite_fset])    
    from assms(1) 
    show "set (map fst (map fst pth)) \<subseteq> fset vertices"
      by (induction v v' pth) (auto, metis valid_edges notin_fset splitD valid_out_port.simps)
  qed
  also have "\<dots> = fcard vertices" by (simp add: fcard.rep_eq)
  finally show ?thesis.
qed

lemma hyps_free_path_not_in_scope:
  assumes "terminal_path v t pth"
  assumes "(v',p') \<in> snd ` set pth"
  shows   "v' \<notin> scope (v, p)"
proof
  assume "v' \<in> scope (v,p)"

  from `(v',p') \<in> snd \` set pth`
  obtain pth1 pth2 e  where "pth = pth1@[e]@pth2" and "snd e = (v',p')" by (rule snd_set_split)
  from terminal_path_is_path[OF assms(1), unfolded `pth = _ `] `snd e = _`
  have "path v v' (pth1@[e])" and "path v' t pth2" unfolding path_split by (auto simp add: edge_end_tup)
  
  from `v' \<in> scope (v,p)` terminal_path_end_is_terminal[OF assms(1)] `path v' t pth2`
  have "(v,p) \<in> snd ` set pth2" by (rule scope_find)
  then obtain pth2a e' pth2b  where "pth2 = pth2a@[e']@pth2b" and "snd e' = (v,p)"  by (rule snd_set_split)
  from `path v' t pth2`[unfolded `pth2 = _ `] `snd e' = _`
  have "path v' v (pth2a@[e'])" and "path v t pth2b" unfolding path_split by (auto simp add: edge_end_tup)
  
  from `path v v' (pth1@[e])` `path v' v (pth2a@[e'])`
  have "path v v ((pth1@[e])@(pth2a@[e']))" by (rule path_appendI)
  moreover
  from terminal_path_is_hyps_free[OF assms(1)] `pth = _` `pth2 = _`
  have "hyps_free ((pth1@[e])@(pth2a@[e']))" by (auto simp add: hyps_free_def)
  ultimately
  have "((pth1@[e])@(pth2a@[e'])) = []" by (rule hyps_free_acyclic)
  thus False by simp
qed

end

locale Saturated_Graph = Port_Graph +
  assumes saturated: "valid_in_port (v,p) \<Longrightarrow> \<exists> e \<in> edges . snd e = (v,p)"

locale Well_Shaped_Graph =  Well_Scoped_Graph + Acyclic_Graph + Saturated_Graph + Pruned_Port_Graph

locale Labeled_Signature = 
  Port_Graph_Signature_Scoped +
  fixes labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'preform" 
  fixes labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'preform" 

locale Instantiation =
  Port_Graph nodes _ _ vertices _ edges +
  Labeled_Signature nodes  _ _ _ labelsIn labelsOut +
  Abstract_Formulas freshen pre_fv _ subst
  for nodes :: "'node stream" and edges :: "('vertex, 'outPort, 'inPort) edge set" and vertices :: "'vertex fset" and labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'preform" and labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'preform" 
  and pre_fv :: "'preform \<Rightarrow> 'var set" and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" and freshen :: "'vertex \<Rightarrow> 'preform \<Rightarrow> 'form" +
  fixes inst :: "'vertex \<Rightarrow> 'subst"
begin
  definition labelAtIn :: "'vertex \<Rightarrow> 'inPort \<Rightarrow> 'form"  where
    "labelAtIn v p = subst (inst v) (freshen v (labelsIn (nodeOf v) p))"
  definition labelAtOut :: "'vertex \<Rightarrow> 'outPort \<Rightarrow> 'form"  where
    "labelAtOut v p = subst (inst v) (freshen v (labelsOut (nodeOf v) p))"
end

locale Solution =
  Instantiation _ _ _ _ _ _ _ _ edges for edges :: "(('vertex \<times> 'outPort) \<times> 'vertex \<times> 'inPort) set" +
  assumes solved: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> labelAtOut v\<^sub>1 p\<^sub>1 = labelAtIn v\<^sub>2 p\<^sub>2"

locale Proof_Graph =  Well_Shaped_Graph + Solution


locale Port_Graph_Signature_Scoped_Vars =
  Port_Graph_Signature nodes inPorts outPorts +
  Abstract_Formulas freshen pre_fv _ subst
  for nodes :: "'node stream" and inPorts :: "'node \<Rightarrow> 'inPort fset"  and outPorts :: "'node \<Rightarrow> 'outPort fset"
  and pre_fv :: "'preform \<Rightarrow> 'var set" and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" and freshen :: "'vertex \<Rightarrow> 'preform \<Rightarrow> 'form" +
  fixes local_vars :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'var set"

locale Well_Scoped_Instantiation =
   Instantiation  inPorts outPorts nodeOf hyps fv ran_fv closed nodes edges vertices labelsIn labelsOut pre_fv subst freshen inst +
   Port_Graph_Signature_Scoped_Vars fv ran_fv closed nodes  inPorts outPorts pre_fv subst freshen local_vars
   for inPorts :: "'node \<Rightarrow> 'inPort fset" 
    and outPorts :: "'node \<Rightarrow> 'outPort fset" 
    and nodeOf :: "'vertex \<Rightarrow> 'node" 
    and hyps :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'inPort option" 
    and fv :: "'form \<Rightarrow> ('var \<times> 'vertex) set" 
    and ran_fv :: "'subst \<Rightarrow> ('var \<times> 'vertex) set" 
    and closed :: "'preform \<Rightarrow> bool" 
    and nodes :: "'node stream" 
    and vertices :: "'vertex fset" 
    and labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'preform" 
    and labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'preform" 
    and pre_fv :: "'preform \<Rightarrow> 'var set" 
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and freshen :: "'vertex \<Rightarrow> 'preform \<Rightarrow> 'form" 
    and inst :: "'vertex \<Rightarrow> 'subst" 
    and edges :: "('vertex, 'outPort, 'inPort) edge set" 
    and local_vars :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'var set" +
  assumes well_scoped_inst: "valid_in_port (v,p) \<Longrightarrow> var \<in> local_vars (nodeOf v) p \<Longrightarrow> freshenV v var \<in> ran_fv (inst v') \<Longrightarrow> v' \<in> scope (v,p)"
begin
  lemma out_of_scope: "valid_in_port (v,p) \<Longrightarrow> v' \<notin> scope (v,p) \<Longrightarrow> freshenV v ` local_vars (nodeOf v) p \<inter> ran_fv (inst v') = {}"
    using well_scoped_inst by auto
end
  

locale Scoped_Proof_Graph =
  Well_Shaped_Graph  nodes inPorts outPorts vertices nodeOf edges hyps  +
  Solution inPorts outPorts nodeOf hyps fv ran_fv closed nodes vertices labelsIn labelsOut pre_fv subst freshen inst edges +
  Well_Scoped_Instantiation inPorts outPorts nodeOf hyps fv ran_fv closed nodes vertices labelsIn labelsOut pre_fv subst freshen inst edges local_vars
   for inPorts :: "'node \<Rightarrow> 'inPort fset" 
    and outPorts :: "'node \<Rightarrow> 'outPort fset" 
    and nodeOf :: "'vertex \<Rightarrow> 'node" 
    and hyps :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'inPort option" 
    and fv :: "'form \<Rightarrow> ('var \<times> 'vertex) set" 
    and ran_fv :: "'subst \<Rightarrow> ('var \<times> 'vertex) set" 
    and closed :: "'preform \<Rightarrow> bool" 
    and nodes :: "'node stream" 
    and vertices :: "'vertex fset" 
    and labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'preform" 
    and labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'preform" 
    and pre_fv :: "'preform \<Rightarrow> 'var set" 
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and freshen :: "'vertex \<Rightarrow> 'preform \<Rightarrow> 'form" 
    and inst :: "'vertex \<Rightarrow> 'subst" 
    and edges :: "('vertex, 'outPort, 'inPort) edge  set" 
    and local_vars :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'var set"


datatype ('preform, 'rule) graph_node = Assumption 'preform | Conclusion 'preform | Rule 'rule

type_synonym ('preform, 'var) in_port = "('preform, 'var) antecedent"
datatype ('preform, 'var) out_port = Reg 'preform | Hyp 'preform "('preform, 'var) in_port"
type_synonym ('v, 'preform, 'var) edge' = "(('v \<times> ('preform, 'var) out_port) \<times> ('v \<times> ('preform, 'var) in_port))"


context Abstract_Task
begin
  definition nodes :: "('preform, 'rule) graph_node stream" where
    "nodes = shift (map Assumption assumptions) (shift (map Conclusion conclusions) (smap Rule rules))"

  fun inPorts where
    "inPorts (Rule r) = f_antecedent r"
   |"inPorts (Assumption r) = {||}"
   |"inPorts (Conclusion r) = {| plain_ant r |}"

  definition outPortsRule where
    "outPortsRule r = ffUnion ((\<lambda> a. (\<lambda> h. Hyp h a) |`| a_hyps a) |`| f_antecedent r) |\<union>| Reg |`| f_consequent r"

  lemma Reg_in_outPortsRule[simp]:  "Reg c |\<in>| outPortsRule r \<longleftrightarrow> c |\<in>| f_consequent r"
    by (auto simp add: outPortsRule_def fmember.rep_eq ffUnion.rep_eq)
  lemma Hyp_in_outPortsRule[simp]:  "Hyp h c |\<in>| outPortsRule r \<longleftrightarrow> c |\<in>| f_antecedent r \<and> h |\<in>| a_hyps c"
    by (auto simp add: outPortsRule_def fmember.rep_eq ffUnion.rep_eq)

  fun outPorts where
    "outPorts (Rule r) = outPortsRule r"
   |"outPorts (Assumption r) = {|Reg r|}"
   |"outPorts (Conclusion r) = {||}"

  fun labelsIn where
    "labelsIn _ p = a_conc p"

  fun labelsOut where
    "labelsOut _ (Reg p) = p"
   | "labelsOut _ (Hyp h c) = h"

  fun hyps where 
     "hyps (Rule r) (Hyp h a) = (if a |\<in>| f_antecedent r \<and> h |\<in>| a_hyps a then Some a else None)"
   | "hyps _ _ = None"

  fun local_vars :: "('preform, 'rule) graph_node \<Rightarrow> ('preform, 'var) in_port \<Rightarrow> 'var set"  where
     "local_vars _ a = a_fresh a"

end


locale Tasked_Signature = Abstract_Task 
begin
  sublocale Labeled_Signature nodes inPorts outPorts hyps labelsIn labelsOut
  proof
    case (goal1 n p1 p2)
    thus ?case by(induction n p1 rule: hyps.induct) (auto  split: if_splits)
  qed
end

locale Tasked_Proof_Graph =
  Tasked_Signature ran_fv closed freshen pre_fv fv subst antecedent consequent rules assumptions conclusions  +
  Scoped_Proof_Graph inPorts outPorts nodeOf hyps fv ran_fv closed nodes vertices labelsIn labelsOut pre_fv subst freshen inst edges local_vars
  for freshen :: "'vertex \<Rightarrow> 'preform \<Rightarrow> 'form" 
    and fv :: "'form \<Rightarrow> ('var \<times> 'vertex) set" 
    and ran_fv :: "'subst \<Rightarrow> ('var \<times> 'vertex) set" 
    and closed :: "'preform \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and pre_fv :: "'preform \<Rightarrow> 'var set" 

    and antecedent :: "'rule \<Rightarrow> ('preform, 'var) antecedent list" 
    and consequent :: "'rule \<Rightarrow> 'preform list" 
    and fresh_vars :: "'rule \<Rightarrow> 'var set"
    and rules :: "'rule stream" 

    and assumptions :: "'preform list" 
    and conclusions :: "'preform list" 

    and vertices :: "'vertex fset" 
    and nodeOf :: "'vertex \<Rightarrow> ('preform, 'rule) graph_node" 
    and edges :: "('vertex, 'preform, 'var) edge' set" 
    and inst :: "'vertex \<Rightarrow> 'subst"  +
  assumes conclusions_present: "set (map Conclusion conclusions) \<subseteq> nodeOf ` fset vertices"
begin
  lemma hyps_for_conclusion[simp]: "hyps_for (Conclusion n) p = {||}"
    using hyps_for_subset by auto
end

end