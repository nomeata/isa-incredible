theory Incredible_Correctness
imports
  Incredible_Deduction
  Natural_Deduction
begin

context Tasked_Proof_Graph
begin

  definition adjacentTo :: "'vertex \<Rightarrow> 'preform in_port \<Rightarrow> ('vertex \<times> 'preform out_port)" where
   "adjacentTo v p = (SOME ps. (ps, (v,p)) \<in> edges)" 
  
  fun rule_for ::  "('vertex \<times> 'preform out_port) \<Rightarrow> ('rule \<times> 'preform) NatRule" where
    "rule_for (v, p) =
        (case p of Hyp h c \<Rightarrow> Axiom
                 | Reg c \<Rightarrow> (case nodeOf v of Rule r \<Rightarrow> NatRule (r,c)
                                            | Assumption a \<Rightarrow> Axiom))"

  fun isReg  where
    "isReg v p = (case p of Hyp h c \<Rightarrow> None | Reg  c \<Rightarrow>
        (case nodeOf v of Assumption a \<Rightarrow> None | Rule r \<Rightarrow>
        Some (r,c)
        ))"

  fun extra_assms :: "'vertex \<Rightarrow> 'preform in_port \<Rightarrow> 'form fset" where
    "extra_assms v p = (\<lambda> p. labelAtOut v p) |`| hyps_for (nodeOf v) p"

  primcorec tree :: "'form fset \<Rightarrow> 'vertex \<Rightarrow> 'preform in_port \<Rightarrow> (('form fset \<times> 'form), ('rule \<times> 'preform) NatRule) dtree" where
   "root (tree \<Gamma> v p) =
      ((\<Gamma>, labelAtIn v p),
      (case adjacentTo v p of (v', p') \<Rightarrow>
      (case isReg v' p' of None \<Rightarrow> Axiom | Some (r, c) \<Rightarrow> NatRule (r,c))
      ))"
   | "cont (tree \<Gamma> v p) =
      (case adjacentTo v p of (v', p') \<Rightarrow>
      (case isReg v' p' of None \<Rightarrow> {||} | Some (r, c) \<Rightarrow>
      ((\<lambda> p. tree (extra_assms v' p |\<union>| \<Gamma>) v' p) |`| inPorts (nodeOf v'))
      ))"

lemma fst_root_tree[simp]: "fst (root (tree \<Gamma> v p)) = (\<Gamma>, labelAtIn v p)" by simp

lemma fst_root_tree_comp[simp]: "fst \<circ> root \<circ> tree \<Gamma> v = (\<lambda> p. (\<Gamma>, labelAtIn v p))" by auto

inductive_set global_assms where
  "v |\<in>| vertices \<Longrightarrow> nodeOf v = Assumption p \<Longrightarrow> labelAtOut v (Reg p) \<in> global_assms"

inductive_set local_assms for v p pth t where
  "(v',p') \<in> insert (v,p) (snd ` set pth) \<Longrightarrow> h |\<in>| hyps_for (nodeOf v') p' \<Longrightarrow> labelAtOut v' h \<in> local_assms v p pth t"

lemma local_assms_cons:
  "local_assms v' a (((v', p'), (v, p))#pth) t = labelAtOut v' ` fset (hyps_for (nodeOf v') a) \<union> local_assms v p pth t"
  apply (auto 4 4 simp add: local_assms.simps )
  apply (auto 4 4 simp add: image_iff)
  apply (metis  snd_conv)
  apply (metis surjective_pairing)
  apply fastforce
  done

lemma out_port_cases[consumes 1, case_names Assumption Hyp Rule]:
  assumes "p |\<in>| outPorts n"
  obtains
    a where "n = Assumption a" and "p = Reg a"
    | r h c where "n = Rule r" and "p = Hyp h c"
    | r f where "n = Rule r" and "p = Reg f"
  using assms by (atomize_elim, cases p; cases n) auto

  
theorem correctness:
  assumes "v |\<in>| vertices"
  assumes "p |\<in>| inPorts (nodeOf v)"
  assumes "global_assms \<subseteq> fset \<Gamma>"
  assumes "terminal_vertex t"
  assumes "path v t pth"
  assumes "local_assms v p pth t \<subseteq> fset \<Gamma>"
  shows "wf (tree \<Gamma> v p)"
using assms
proof (coinduction arbitrary: \<Gamma> v p pth)
case (wf \<Gamma> v p pth)
  let ?t = "tree \<Gamma> v p"
  from saturated[OF wf(1,2)]
  obtain v' p'
  where e:"((v',p'),(v,p)) \<in> edges" and [simp]: "adjacentTo v p = (v',p')"
    by (auto simp add: adjacentTo_def, metis (no_types, lifting) eq_fst_iff tfl_some)

  let ?l = "labelAtIn v p"
  
  from e valid_edges have "v' |\<in>| vertices" and "p' |\<in>| outPorts (nodeOf v')" by auto
  hence "nodeOf v' \<in> sset nodes" using valid_nodes by (meson image_eqI notin_fset set_mp)

  from `((v', p'), (v, p)) \<in> edges`
  have s: "labelAtOut v' p' = labelAtIn v p"  by (rule solved)

  from `p' |\<in>| outPorts (nodeOf v')`
  show ?case
  proof (cases rule: out_port_cases)
    case (Hyp r h c)

    from Hyp `p' |\<in>| outPorts (nodeOf v')`
    have "h \<in> set (fst c)" and "c \<in> set (antecedent r)" by auto
    hence "hyps (nodeOf v') (Hyp h c) = Some c" using Hyp by simp

    from well_scoped[OF ` _ \<in> edges`[unfolded Hyp] this]
    have "(v, p) = (v', c) \<or> v \<in> scope (v', c)".
    hence "(v', c) \<in> insert (v, p) (snd ` set pth)"
    proof
      assume "(v, p) = (v', c)"
      thus ?thesis by simp
    next
      assume "v \<in> scope (v', c)"
      from this `terminal_vertex t` `path v t pth`
      have "(v', c) \<in> snd ` set pth" by (rule scope_find)
      thus ?thesis by simp
    qed
    moreover

    
    from `hyps (nodeOf v') (Hyp h c) = Some c`
    have "(Hyp h c) |\<in>| hyps_for (nodeOf v') c" by simp
    ultimately

    have "labelAtOut v' (Hyp h c) \<in> local_assms v p pth t"..
    with `local_assms v p pth t \<subseteq> fset \<Gamma>`
    have "labelAtOut v' (Hyp h c) \<in> fset \<Gamma>" by (rule subsetD)
    hence "labelAtIn v p |\<in>| \<Gamma>"  by (simp add: s[symmetric] Hyp fmember.rep_eq)
    thus ?thesis using Hyp by (auto intro: exI[where x = ?t])
  next
    case (Assumption f)

    from `v' |\<in>| vertices` `nodeOf v' = Assumption f`
    have "labelAtOut v' (Reg f) \<in> global_assms"
      by (rule global_assms.intros)
    with `global_assms \<subseteq> fset \<Gamma>`
    have "labelAtOut v' (Reg f) \<in> fset \<Gamma>" by (rule subsetD)
    hence "labelAtIn v p |\<in>| \<Gamma>" by (simp add: s[symmetric] Assumption fmember.rep_eq)
    thus ?thesis using Assumption
      by (auto intro: exI[where x = ?t])
  next
    case (Rule r f)
    with `nodeOf v' \<in> sset nodes`
    have "r \<in> sset rules"
      by (auto simp add: nodes_def stream.set_map)
    moreover

    from Rule  `p' |\<in>| outPorts (nodeOf v')`
    have "f \<in> set (consequent r)"
      by auto
    moreover

    {
      fix x p h
      assume 1: "x \<in> set (antecedent r)"
      have "hyps_for (nodeOf v') x = fset_from_list (map (\<lambda> f. Hyp f x) (fst x))"
        apply (rule fset_eqI)
        apply (rename_tac p')
        apply (case_tac p')
        using 1
        apply (auto simp add: Rule split: if_splits)
        done
    }
    note * = this

    from `f \<in> set (consequent r)`
    have "natEff_Inst (r, f) f (fset_from_list (map (apfst fset_from_list) (antecedent r)))" 
      by (rule natEff_Inst.intros)
    hence "natEff (r, f) (subst (inst v') (annotate v' f))
           ((\<lambda>n. ((\<lambda>p. subst (inst v') (annotate v' p)) |`| fst n, subst (inst v') (annotate v' (snd n)))) |`| fset_from_list (map (apfst fset_from_list) (antecedent r)))"
          (is "natEff _ _ ?ant")
      by (rule natEff.intros)
    from effNatRuleI[OF this]
    have "eff (NatRule (r, f)) (\<Gamma>, subst (inst v') (annotate v' f)) (fset_from_list (map (\<lambda>x. (fset_from_list (map (\<lambda>p. subst (inst v') (annotate v' p)) (fst x)) |\<union>| \<Gamma>, subst (inst v') (annotate v' (snd x)))) (antecedent r)))"
      by (auto simp del: eff.simps simp add: comp_def)
    hence "eff (NatRule (r, f)) (\<Gamma>, labelAtOut v' p') (fset_from_list (map (\<lambda>x. (fset_from_list (map (\<lambda>p. labelAtOut v' (Hyp p x)) (fst x)) |\<union>| \<Gamma>, labelAtIn v' x)) (antecedent r)))"
      using Rule by (auto simp add: labelAtOut_def labelAtIn_def simp del: eff.simps)
    hence "eff (NatRule (r, f)) (\<Gamma>, labelAtIn v p) (fset_from_list (map (\<lambda> a. (extra_assms v' a |\<union>| \<Gamma>, labelAtIn v' a)) (antecedent r)))"
      apply (simp add: s del: eff.simps)        
      apply (erule back_subst) back back 
      apply (rule map_cong[OF refl])
      apply (rule arg_cong) back back
      apply (subst *)
      apply assumption
      apply simp
      apply (simp add: comp_def)
      done
    moreover

    { fix x
      assume "x |\<in>| cont ?t"
      then obtain a where "x = tree (labelAtOut  v' |`| hyps_for (Rule r) a |\<union>| \<Gamma>) v' a" and "a \<in> set (antecedent r)"
        by (auto simp add: Rule)
      note this(1)
      moreover

      note  `v' |\<in>| vertices`
      moreover

      from `a \<in> set (antecedent r)`
      have "a |\<in>| inPorts (nodeOf v')"
        by (simp add: Rule)
      moreover

      from `global_assms \<subseteq> fset \<Gamma>`
      have "global_assms \<subseteq> fset (labelAtOut v' |`| hyps_for (Rule r) a |\<union>| \<Gamma>)" by auto
      moreover

      note `terminal_vertex t`
      moreover

      from `_ \<in> edges` `path v t pth`
      have "path v' t (((v', p'), (v, p))#pth)"  by (simp add: path_cons_simp)
      moreover

      from `local_assms v p pth t \<subseteq> _` Rule
      have "local_assms v' a (((v', p'), (v, p))#pth) t \<subseteq> fset (labelAtOut v' |`| hyps_for (Rule r) a |\<union>| \<Gamma>)"
        by (auto simp add: local_assms_cons)        
      ultimately

      have "\<exists>\<Gamma> v p pth. x = tree \<Gamma> v p \<and> v |\<in>| vertices \<and> p |\<in>| inPorts (nodeOf v) \<and>  global_assms \<subseteq> fset \<Gamma> \<and> terminal_vertex t \<and> path v t pth \<and> local_assms v p pth t \<subseteq> fset \<Gamma>"
        by blast
    }
    ultimately

    show ?thesis using Rule
      by (auto intro!: exI[where x = ?t]  simp add: comp_def stream.set_map no_empty_conclusions n_rules_def comp_assoc[symmetric] simp del: eff.simps)       
  qed
qed

end

end