theory Incredible_Correctness
imports
  Incredible_Deduction
  Natural_Deduction
begin

lemma ffUnion_fempty[simp]: "ffUnion fempty = fempty"
  by (auto simp add: fmember.rep_eq ffUnion.rep_eq)

lemma ffUnion_finsert[simp]: "ffUnion (finsert x S) = x |\<union>| ffUnion S"
  by (auto simp add: fmember.rep_eq ffUnion.rep_eq)



context Tasked_Proof_Graph
begin

  definition adjacentTo :: "'vertex \<Rightarrow> ('preform, 'var) in_port \<Rightarrow> ('vertex \<times> ('preform, 'var) out_port)" where
   "adjacentTo v p = (SOME ps. (ps, (v,p)) \<in> edges)" 
  
  fun isReg where
    "isReg v p = (case p of Hyp h c \<Rightarrow> False | Reg  c \<Rightarrow>
        (case nodeOf v of
          Conclusion a \<Rightarrow> False
        | Assumption a \<Rightarrow> False
        | Rule r \<Rightarrow> True
        | Helper \<Rightarrow> True
        ))"

  fun toNatRule  where
    "toNatRule v p = (case p of Hyp h c \<Rightarrow> Axiom | Reg  c \<Rightarrow>
        (case nodeOf v of
          Conclusion a \<Rightarrow> Axiom (* a lie *)
        | Assumption a \<Rightarrow> Axiom
        | Rule r \<Rightarrow> NatRule (r,c)
        | Helper \<Rightarrow> Cut
        ))"


  inductive_set global_assms' :: "'var itself \<Rightarrow> 'form set" for i  where
    "v |\<in>| vertices \<Longrightarrow> nodeOf v = Assumption p \<Longrightarrow> labelAtOut v (Reg p) \<in> global_assms' i"

  lemma finite_global_assms': "finite (global_assms' i)"
  proof-
    have "finite (fset vertices)" by (rule finite_fset)
    moreover
    have "global_assms' i \<subseteq> (\<lambda> v. case nodeOf v of Assumption p \<Rightarrow>  labelAtOut v (Reg p)) ` fset vertices"
      by (force simp add: global_assms'.simps fmember.rep_eq image_iff )
    ultimately
    show ?thesis by (rule finite_surj)
  qed

  context includes fset.lifting
  begin
  lift_definition global_assms :: "'var itself \<Rightarrow> 'form fset" is global_assms' by (rule finite_global_assms')
  lemmas global_assmsI = global_assms'.intros[Transfer.transferred]
  lemmas global_assms_simps = global_assms'.simps[Transfer.transferred]
  end

  fun extra_assms :: "('vertex \<times> ('preform, 'var) in_port) \<Rightarrow> 'form fset" where
    "extra_assms (v, p) = (\<lambda> p. labelAtOut v p) |`| hyps_for (nodeOf v) p"

  fun hyps_along :: "('vertex, 'preform, 'var) edge' list \<Rightarrow> 'form fset" where
    "hyps_along pth = ffUnion (extra_assms |`| snd |`| fset_from_list pth) |\<union>| global_assms TYPE('var)"

  lemma hyps_alongE[consumes 1, case_names Hyp Assumption]:
    assumes "f |\<in>| hyps_along pth"
    obtains v p h where "(v,p) \<in> snd ` set pth" and "f = labelAtOut v h " and "h |\<in>| hyps_for (nodeOf v) p"
    | v pf  where "v |\<in>| vertices" and "nodeOf v = Assumption pf" "f = labelAtOut v (Reg pf)" 
    using assms
    apply (auto simp add: fmember.rep_eq ffUnion.rep_eq  global_assms_simps[unfolded fmember.rep_eq])
    apply (metis image_iff snd_conv)
    done

  primcorec tree :: "'vertex \<Rightarrow> ('preform, 'var) in_port \<Rightarrow> ('vertex, 'preform, 'var) edge' list \<Rightarrow>  (('form entailment), ('rule \<times> 'preform) NatRule) dtree" where
   "root (tree v p pth) =
      ((hyps_along ((adjacentTo v p,(v,p))#pth) \<turnstile> labelAtIn v p),
      (case adjacentTo v p of (v', p') \<Rightarrow> toNatRule v' p'
      ))"
   | "cont (tree v p pth) =
      (case adjacentTo v p of (v', p') \<Rightarrow>
      (if isReg v' p' then ((\<lambda> p''. tree v' p'' ((adjacentTo v p,(v,p))#pth)) |`| inPorts (nodeOf v')) else {||}
      ))"


lemma fst_root_tree[simp]: "fst (root (tree v p pth)) = (hyps_along ((adjacentTo v p,(v,p))#pth) \<turnstile> labelAtIn v p)" by simp

(*
lemma fst_root_tree_comp[simp]: "fst \<circ> root \<circ> tree \<Gamma> v = (\<lambda> p. (hyps_along pth \<turnstile> labelAtIn v p))" by auto
*)


lemma out_port_cases[consumes 1, case_names Assumption Hyp Rule Helper]:
  assumes "p |\<in>| outPorts n"
  obtains
    a where "n = Assumption a" and "p = Reg a"
    | r h c where "n = Rule r" and "p = Hyp h c"
    | r f where "n = Rule r" and "p = Reg f"
    | "n = Helper" and "p = Reg anyP"
  using assms by (atomize_elim, cases p; cases n) auto

lemma hyps_for_fimage: "hyps_for (Rule r) x = (if x |\<in>| f_antecedent r then (\<lambda> f. Hyp f x) |`| (a_hyps x) else {||})"
  apply (rule fset_eqI)
  apply (rename_tac p')
  apply (case_tac p')
  apply (auto simp add:  split: if_splits out_port.splits)
  done

theorem wf_tree:
  assumes "valid_in_port (v,p)"
  assumes "terminal_path v t pth"
  shows "wf (tree v p pth)"
using assms
proof (coinduction arbitrary: v p pth)
case (wf v p pth)
  let ?t = "tree v p pth"
  from saturated[OF wf(1)]
  obtain v' p'
  where e:"((v',p'),(v,p)) \<in> edges" and [simp]: "adjacentTo v p = (v',p')"
    by (auto simp add: adjacentTo_def, metis (no_types, lifting) eq_fst_iff tfl_some)

  let ?e = "((v',p'),(v,p))"
  let ?pth' = "?e#pth"
  let ?\<Gamma> = "hyps_along ?pth'"
  let ?l = "labelAtIn v p"
  
  from e valid_edges have "v' |\<in>| vertices" and "p' |\<in>| outPorts (nodeOf v')" by auto
  hence "nodeOf v' \<in> sset nodes" using valid_nodes by (meson image_eqI notin_fset set_mp)

  from `?e \<in> edges`
  have s: "labelAtOut v' p' = labelAtIn v p"  by (rule solved)

  from `p' |\<in>| outPorts (nodeOf v')`
  show ?case
  proof (cases rule: out_port_cases)
    case (Hyp r h c)

    from Hyp `p' |\<in>| outPorts (nodeOf v')`
    have "h |\<in>| a_hyps c" and "c |\<in>| f_antecedent r" by auto
    hence "hyps (nodeOf v') (Hyp h c) = Some c" using Hyp by simp

    from well_scoped[OF ` _ \<in> edges`[unfolded Hyp] this]
    have "(v, p) = (v', c) \<or> v \<in> scope (v', c)".
    hence "(v', c) \<in> insert (v, p) (snd ` set pth)"
    proof
      assume "(v, p) = (v', c)"
      thus ?thesis by simp
    next
      assume "v \<in> scope (v', c)"
      from this terminal_path_end_is_terminal[OF wf(2)] terminal_path_is_path[OF wf(2)]
      have "(v', c) \<in> snd ` set pth" by (rule scope_find)
      thus ?thesis by simp
    qed
    moreover

    
    from `hyps (nodeOf v') (Hyp h c) = Some c`
    have "Hyp h c |\<in>| hyps_for (nodeOf v') c" by simp
    hence "labelAtOut v' (Hyp h c) |\<in>| extra_assms (v',c)" by auto
    ultimately

    have "labelAtOut v' (Hyp h c) |\<in>| ?\<Gamma>" 
      by (fastforce simp add: fmember.rep_eq ffUnion.rep_eq)
      
    hence "labelAtIn v p |\<in>| ?\<Gamma>" by (simp add: s[symmetric] Hyp fmember.rep_eq)
    thus ?thesis
      using Hyp
      apply (auto intro: exI[where x = ?t] simp add: eff.simps simp del: hyps_along.simps)
      done
  next
    case (Assumption f)

    from `v' |\<in>| vertices` `nodeOf v' = Assumption f`
    have "labelAtOut v' (Reg f) |\<in>| global_assms TYPE('var)"
      by (rule global_assmsI)
    hence "labelAtOut v' (Reg f) |\<in>| ?\<Gamma>" by auto
    hence "labelAtIn v p |\<in>| ?\<Gamma>" by (simp add: s[symmetric] Assumption fmember.rep_eq)
    thus ?thesis using Assumption
      by (auto intro: exI[where x = ?t] simp add: eff.simps)
  next
    case (Rule r f)
    with `nodeOf v' \<in> sset nodes`
    have "r \<in> sset rules"
      by (auto simp add: nodes_def stream.set_map)

    from Rule
    have "hyps (nodeOf v') p' = None" by simp
    with e `terminal_path v t pth`
    have "terminal_path v' t ?pth'"..

    from Rule  `p' |\<in>| outPorts (nodeOf v')`
    have "f |\<in>| f_consequent r" by simp
    hence "f \<in> set (consequent r)" by (simp add: f_consequent_def)
    with `r \<in> sset rules`
    have "NatRule (r, f) \<in> sset (smap NatRule n_rules)"
      by (auto simp add: stream.set_map n_rules_def no_empty_conclusions)
    moreover

    {
    from `f |\<in>| f_consequent r`
    have "f \<in> set (consequent r)" by (simp add: f_consequent_def)
    hence "natEff_Inst (r, f) f (f_antecedent r)" 
      by (rule natEff_Inst.intros)
    hence "eff (NatRule (r, f)) (?\<Gamma> \<turnstile> subst (inst v') (freshen (fidx vertices v') f))
           ((\<lambda>ant. ((\<lambda>p. subst (inst v') (freshen (fidx vertices v') p)) |`| a_hyps ant |\<union>| ?\<Gamma> \<turnstile> subst (inst v') (freshen (fidx vertices v') (a_conc ant)))) |`| f_antecedent r)" 
           (is "eff _ _ ?ants")
    proof (rule eff.intros)
      fix ant f
      assume "ant |\<in>| f_antecedent r"
      from  `v' |\<in>| vertices` `ant |\<in>| f_antecedent r`
      have "valid_in_port (v',ant)" by (simp add: Rule)

      assume "f |\<in>| ?\<Gamma>"
      thus "freshenV (fidx vertices v') ` a_fresh ant \<inter> fv f = {}" 
      proof(induct rule: hyps_alongE)
        case (Hyp v'' p'' h'')

        from Hyp(1) snd_set_path_verties[OF terminal_path_is_path[OF `terminal_path v' t ?pth'`]]
        have "v'' |\<in>| vertices" by (force simp add: fmember.rep_eq)

        from `terminal_path v' t ?pth'` Hyp(1)
        have "v'' \<notin> scope (v', ant)" by (rule hyps_free_path_not_in_scope)
        with `valid_in_port (v',ant)`
        have "freshenV (fidx vertices v') ` local_vars (nodeOf v') ant \<inter> ran_fv (inst v'') = {}"
         by (rule out_of_scope)
        moreover
        from hyps_free_vertices_distinct'[OF `terminal_path v' t ?pth'`] Hyp.hyps(1)
        have "v'' \<noteq> v'" by (metis distinct.simps(2) fst_conv image_eqI list.set_map)
        hence "fidx vertices v'' \<noteq> fidx vertices v'" using `v' |\<in>| vertices` `v'' |\<in>| vertices` by simp
        hence "freshenV (fidx vertices v') ` a_fresh ant \<inter> freshenV (fidx vertices v'') ` pre_fv (labelsOut (nodeOf v'') h'') = {}"
          by (auto simp add: freshenV_eq_iff)
        moreover
        have "fv f \<subseteq> fv (freshen (fidx vertices v'') (labelsOut (nodeOf v'') h'')) \<union> ran_fv (inst v'') " using `f = _`
          by (simp add: labelAtOut_def fv_subst)
        ultimately
        show ?thesis by (fastforce simp add: fv_freshen)
      next
        case (Assumption v pf)
        hence "f = subst (inst v) (freshen (fidx vertices v) pf)" by (simp add: labelAtOut_def)
        moreover
        from Assumption have "Assumption pf \<in> sset nodes" using valid_nodes by (auto simp add: fmember.rep_eq)
        hence "pf \<in> set assumptions" unfolding nodes_def by (auto simp add: stream.set_map)
        hence "closed pf" using assumptions_closed by auto
        ultimately
        have "fv f = {}" using closed_pre_fv subst_no_vars fv_freshen by blast
        thus ?thesis by simp
      qed      
    next
      fix ant
      assume "ant |\<in>| f_antecedent r"
      from  `v' |\<in>| vertices` `ant |\<in>| f_antecedent r`
      have "valid_in_port (v',ant)" by (simp add: Rule)
      moreover
      from `v' |\<in>| vertices`
      have "v' \<notin> scope (v', ant)" by (rule scopes_not_refl)
      ultimately
      have "freshenV (fidx vertices v') ` local_vars (nodeOf v') ant \<inter> ran_fv (inst v') = {}"
        by (rule out_of_scope)
      thus "freshenV (fidx vertices v') ` a_fresh ant \<inter> ran_fv (inst v') = {}" by simp
    qed
    also
    have "subst (inst v') (freshen (fidx vertices v') f) = labelAtOut v' p'" using Rule by (simp add: labelAtOut_def)
    also
    note `labelAtOut v' p' = labelAtIn v p`
    also
    have "?ants = ((\<lambda>x. (extra_assms (v',x) |\<union>| hyps_along ?pth' \<turnstile> labelAtIn  v' x)) |`| f_antecedent r)"
      by (rule fimage_cong[OF refl])
        (auto simp add: labelAtIn_def labelAtOut_def Rule hyps_for_fimage fmember.rep_eq ffUnion.rep_eq)
    finally
    have "eff (NatRule (r, f))
        (?\<Gamma>, labelAtIn v p)
        ((\<lambda>x. extra_assms (v',x) |\<union>| ?\<Gamma> \<turnstile> labelAtIn v' x) |`| f_antecedent r)".
    }
    moreover

    { fix x
      assume "x |\<in>| cont ?t"
      then obtain a where "x = tree v' a ?pth'" and "a |\<in>| f_antecedent r"
        by (auto simp add: Rule)
      note this(1)
      moreover

      from  `v' |\<in>| vertices` `a |\<in>| f_antecedent r`
      have "valid_in_port (v',a)" by (simp add: Rule)
      moreover

      note `terminal_path v' t ?pth'`
      ultimately

      have "\<exists>v p pth. x = tree v p pth \<and> valid_in_port (v,p) \<and>  terminal_path v t pth"
        by blast
    }
    ultimately

    show ?thesis using Rule
      by (auto intro!: exI[where x = ?t]  simp add: comp_def funion_assoc)
  next
    case Helper
    from Helper
    have "hyps (nodeOf v') p' = None" by simp
    with e `terminal_path v t pth`
    have "terminal_path v' t ?pth'"..

    have "labelAtIn v' (plain_ant anyP) = labelAtIn v p"
      unfolding s[symmetric]
      using Helper by (simp add: labelAtIn_def labelAtOut_def)
    moreover
    { fix x
      assume "x |\<in>| cont ?t"
      
      hence "x = tree v' (plain_ant anyP) ?pth'"
        by (auto simp add: Helper)
      note this(1)
      moreover

      from  `v' |\<in>| vertices`
      have "valid_in_port (v',plain_ant anyP)" by (simp add: Helper)
      moreover

      note `terminal_path v' t ?pth'`
      ultimately

      have "\<exists>v p pth. x = tree v p pth \<and> valid_in_port (v,p) \<and>  terminal_path v t pth"
        by blast
    }
    ultimately

    show ?thesis using Helper
      by (auto intro!: exI[where x = ?t]  simp add: comp_def funion_assoc )
  qed
qed

lemma global_in_ass: "global_assms TYPE('var) |\<subseteq>| ass_forms"
proof
  fix x
  assume "x |\<in>| global_assms TYPE('var)"
  then obtain v pf where "v |\<in>| vertices" and "nodeOf v = Assumption pf" and "x = labelAtOut v (Reg pf)"
    by (auto simp add: global_assms_simps)
  from this (1,2) valid_nodes
  have "Assumption pf \<in> sset nodes" by (auto simp add: fmember.rep_eq)
  hence "pf \<in> set assumptions" by (auto simp add: nodes_def stream.set_map)
  hence "closed pf" using assumptions_closed by auto
  with `x = labelAtOut v (Reg pf)`
  have "x = subst undefined (freshen undefined pf)" by (auto simp add: closed_eq labelAtOut_def)
  thus "x |\<in>| ass_forms" using `pf \<in> set assumptions` by (auto simp add: ass_forms_def)
qed

primcorec edge_tree :: "'vertex \<Rightarrow> ('preform, 'var) in_port \<Rightarrow> ('vertex, 'preform, 'var) edge' tree" where
 "root (edge_tree v p) = (adjacentTo v p, (v,p))"
 | "cont (edge_tree v p) =
    (case adjacentTo v p of (v', p') \<Rightarrow>
    (if isReg v' p' then ((\<lambda> p. edge_tree  v' p) |`| inPorts (nodeOf v')) else {||}
    ))"

lemma tfinite_map_tree: "tfinite (map_tree f t) \<longleftrightarrow> tfinite t"
proof
  assume "tfinite (map_tree f t)"
  thus "tfinite t"
    by (induction "map_tree f t" arbitrary: t rule: tfinite.induct)
       (fastforce intro:  tfinite.intros simp add:  tree.map_sel)
next
  assume "tfinite t"
  thus "tfinite (map_tree f t)"
    by (induction t rule: tfinite.induct)
       (fastforce intro:  tfinite.intros simp add:  tree.map_sel)
qed


lemma finite_tree_edge_tree:
  "tfinite (tree v p pth) \<longleftrightarrow> tfinite (edge_tree v p)"
proof-
  have "map_tree (\<lambda> _. ())  (tree v p pth) = map_tree (\<lambda> _. ()) (edge_tree v p)"
   by(coinduction arbitrary: v p pth)
     (fastforce simp add: tree.map_sel rel_fset_def rel_set_def split: prod.split out_port.split graph_node.split option.split)
  thus ?thesis by (metis tfinite_map_tree)
qed

coinductive forbidden_path :: "'vertex \<Rightarrow> ('vertex, 'preform, 'var) edge' stream \<Rightarrow> bool"   where
    forbidden_path: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = None \<Longrightarrow> forbidden_path v\<^sub>1 pth \<Longrightarrow> forbidden_path v\<^sub>2 (((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2))##pth)"

lemma path_is_forbidden:
  assumes "valid_in_port (v,p)"
  assumes "ipath (edge_tree v p) es"
  shows "forbidden_path v es"
using assms
proof(coinduction arbitrary: v p es)
  case forbidden_path

  let ?es' = "stl es"

  from forbidden_path(2)
  obtain t' where "root (edge_tree v p) = shd es" and "t' |\<in>| cont (edge_tree v p)" and "ipath t' ?es'"
    by rule blast 

  from `root (edge_tree v p) = shd es`
  have [simp]: "shd es = (adjacentTo v p, (v,p))" by simp
    
  from saturated[OF `valid_in_port (v,p)`]
  obtain v' p'
  where e:"((v',p'),(v,p)) \<in> edges" and [simp]: "adjacentTo v p = (v',p')"
    by (auto simp add: adjacentTo_def, metis (no_types, lifting) eq_fst_iff tfl_some)
  let ?e = "((v',p'),(v,p))"

  from e have "p' |\<in>| outPorts (nodeOf v')" using valid_edges by auto
  thus ?case
  proof(cases rule: out_port_cases)
    case Hyp 
    with  `t' |\<in>| cont (edge_tree v p)`
    have False by auto
    thus ?thesis..
  next
    case Assumption 
    with  `t' |\<in>| cont (edge_tree v p)`
    have False by auto
    thus ?thesis..
  next
    case (Rule r f)
    from `t' |\<in>| cont (edge_tree v p)` Rule
    obtain a where [simp]: "t' = edge_tree v' a" and "a |\<in>| f_antecedent r"  by auto

    have "es = ?e ## ?es'" by (cases es rule: stream.exhaust_sel) simp
    moreover
  
    have "?e \<in> edges" using e by simp
    moreover
  
    from `p' = Reg f` `nodeOf v' = Rule r`
    have "hyps (nodeOf v') p' = None" by simp
    moreover
   
    from e valid_edges have "v' |\<in>| vertices"  by auto
    with `nodeOf v' = Rule r` `a |\<in>| f_antecedent r`
    have "valid_in_port (v', a)" by simp
    moreover
  
    have "ipath (edge_tree v' a) ?es'" using `ipath t' _` by simp
    ultimately
  
    show ?thesis by metis
  next
    case Helper
    from `t' |\<in>| cont (edge_tree v p)` Helper
    have [simp]: "t' = edge_tree v' (plain_ant anyP)" by simp

    have "es = ?e ## ?es'" by (cases es rule: stream.exhaust_sel) simp
    moreover
  
    have "?e \<in> edges" using e by simp
    moreover
  
    from `p' = Reg anyP` `nodeOf v' = Helper`
    have "hyps (nodeOf v') p' = None" by simp
    moreover
   
    from e valid_edges have "v' |\<in>| vertices"  by auto
    with `nodeOf v' = Helper`
    have "valid_in_port (v', plain_ant anyP)" by simp
    moreover
  
    have "ipath (edge_tree v' (plain_ant anyP)) ?es'" using `ipath t' _` by simp
    ultimately
  
    show ?thesis by metis
  qed
qed

lemma forbidden_path_prefix_is_path:
  assumes "forbidden_path v es"
  obtains v' where  "path v' v (rev (stake n es))"
  using assms
  apply (atomize_elim)
  apply (induction n arbitrary: v es)
  apply simp
  apply (simp add: path_snoc)
  apply (subst (asm) forbidden_path.simps) back
  apply auto
  done

lemma forbidden_path_prefix_is_hyp_free:
  assumes "forbidden_path v es"
  shows "hyps_free (rev (stake n es))"
  using assms
  apply (induction n arbitrary: v es)
  apply (simp add: hyps_free_def)
  apply (subst (asm) forbidden_path.simps) back
  apply (force simp add: hyps_free_def)
  done


theorem finite_tree:
  assumes "valid_in_port (v,p)"
  assumes "terminal_vertex v"
  shows "tfinite (tree v p pth)"
proof(rule ccontr)
  let ?n = "Suc (fcard vertices)"
  assume "\<not> tfinite (tree v p pth)"
  hence "\<not> tfinite (edge_tree v p)" unfolding finite_tree_edge_tree.
  then obtain es  :: "('vertex, 'preform, 'var) edge' stream"
    where "ipath (edge_tree v p) es" using Konig by blast
  with `valid_in_port (v,p)`
  have "forbidden_path v es" by (rule path_is_forbidden)
  from forbidden_path_prefix_is_path[OF this] forbidden_path_prefix_is_hyp_free[OF this]
  obtain v' where "path v' v (rev (stake ?n es))" and "hyps_free (rev (stake ?n es))"
    by blast
  from this `terminal_vertex v`
  have "terminal_path  v' v (rev (stake ?n es))" by (rule terminal_pathI)
  hence "length (rev (stake ?n es)) \<le> fcard vertices"
    by (rule hyps_free_limited)
  thus False by simp
qed

lemma solved
unfolding solved_def
proof(intro ballI allI conjI impI)
  fix c
  assume "c |\<in>| conc_forms"
  then obtain pf where "pf \<in> set conclusions" and "c = subst undefined (freshen undefined pf)"
    by (auto simp add: conc_forms_def)
  from this(1) conclusions_present
  obtain v where "v |\<in>| vertices" and "nodeOf v = Conclusion pf"
    by (auto, metis (no_types, lifting) image_iff image_subset_iff notin_fset)

  have "valid_in_port (v, (plain_ant pf))"
    using `v |\<in>| vertices` `nodeOf _ = _ `  by simp

  have "terminal_vertex v" using `nodeOf v = Conclusion pf` by auto

  let ?t = "tree v (plain_ant pf) []"

  have "fst (root ?t) = (global_assms TYPE('var), c)"
    using `pf \<in> set conclusions` `c = _` `nodeOf _ = _`
    by (simp add: labelAtIn_def closed_eq conclusions_closed)
  moreover

  have "global_assms TYPE('var) |\<subseteq>| ass_forms" by (rule global_in_ass)
  moreover

  from  `terminal_vertex v`
  have "terminal_path v v []" by (rule terminal_path_empty)
  with `valid_in_port (v, (plain_ant pf))`
  have "wf ?t" by (rule wf_tree)
  moreover

  from `valid_in_port (v, plain_ant pf)` `terminal_vertex v`
  have "tfinite ?t" by (rule finite_tree)
  ultimately
  
  show "\<exists>\<Gamma> t. fst (root t) = (\<Gamma> \<turnstile> c) \<and> \<Gamma> |\<subseteq>| ass_forms \<and> wf t \<and> tfinite t" by blast
qed

end

end