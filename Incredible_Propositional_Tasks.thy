theory Incredible_Propositional_Tasks
imports Incredible_Propositional
begin

subsubsection \<open>Task 1.1\<close>

interpretation task1_1: Abstract_Task
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[Const (C ''A'') []]"
  "[Const (C ''A'') []]"
by unfold_locales simp

lemma "task1_1.solved"
  unfolding task1_1.solved_def
apply clarsimp
apply (rule_tac x="{|Const (C ''A'') []|}" in exI)
apply clarsimp
apply (rule_tac x="Node ({|Const (C ''A'') []|} \<turnstile> Const (C ''A'') [], Axiom) {||}" in exI)
apply clarsimp
apply (rule conjI)
 apply (rule task1_1.wf)
   apply clarsimp
  apply clarsimp
  apply (rule task1_1.eff.intros(1))
  apply simp
 apply clarsimp
by (auto intro: tfinite.intros)

print_locale Vertex_Graph

interpretation task1_1: Vertex_Graph task1_1.nodes task1_1.inPorts task1_1.outPorts "{|0::nat,1|}"
  "undefined(0 := Assumption (Const (C ''A'') []), 1 := Conclusion (Const (C ''A'') []))"
.
print_locale Pre_Port_Graph
interpretation task1_1: Pre_Port_Graph task1_1.nodes task1_1.inPorts task1_1.outPorts "{|0::nat,1|}"
  "undefined(0 := Assumption (Const (C ''A'') []), 1 := Conclusion (Const (C ''A'') []))"
  "{((0,Reg (Const (C ''A'') [])),(1,plain_ant (Const (C ''A'') [])))}"
.

print_locale Instantiation
interpretation task1_1: Instantiation
  task1_1.inPorts
  task1_1.outPorts
  "undefined(0 := Assumption (Const (C ''A'') []), 1 := Conclusion (Const (C ''A'') []))"
  task1_1.hyps
  task1_1.nodes
  "{((0,Reg (Const (C ''A'') [])),(1,plain_ant (Const (C ''A'') [])))}"
  "{|0::nat,1|}"
  task1_1.labelsIn
  task1_1.labelsOut
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  "id"
  "undefined"
by unfold_locales simp

declare One_nat_def [simp del]

lemma path_one_edge[simp]:
  "task1_1.path v1 v2 pth \<longleftrightarrow>
    (v1 = 0 \<and> v2 = 1 \<and> pth = [((0,Reg (Const (C ''A'') [])),(1,plain_ant (Const (C ''A'') [])))] \<or>
    pth = [] \<and> v1 = v2)"
  apply (cases pth)
  apply (auto simp add: task1_1.path_cons_simp')
  apply (rename_tac list, case_tac list, auto simp add: task1_1.path_cons_simp')+
  done

interpretation Tasked_Proof_Graph
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[Const (C ''A'') []]"
  "[Const (C ''A'') []]"
  "{|0::nat,1|}"
  "undefined(0 := Assumption (Const (C ''A'') []), 1 := Conclusion (Const (C ''A'') []))"
  "{((0,Reg (Const (C ''A'') [])),(1,plain_ant (Const (C ''A'') [])))}"
  "id"
  "undefined"
apply unfold_locales
        apply simp
       apply clarsimp
      apply clarsimp
     apply clarsimp
    apply fastforce
   apply fastforce
  apply (clarsimp simp add: task1_1.labelAtOut_def task1_1.labelAtIn_def)
 apply clarsimp
apply clarsimp
done


end