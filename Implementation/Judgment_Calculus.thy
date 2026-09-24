theory Judgment_Calculus
  imports "Rec_Semantics" "Trace_Formula_Implication"
begin

definition judgment_valid ::
    "(stm_var \<Rightarrow> trace set) \<Rightarrow> Rec \<Rightarrow> trace_formula \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>_ _:_" [70, 70, 70] 70) where
  "\<Turnstile>\<^sub>\<I> \<S>:\<phi> = (\<forall>\<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>\<S>\<rbrakk>\<^sub>\<I> \<subseteq> \<lbrakk>\<phi>\<rbrakk>\<^sub>\<V>)"

definition sequent_valid ::
    "(string \<times> S \<times> trace_formula) list \<Rightarrow> (method_name, S) fmap \<Rightarrow>
      S \<Rightarrow> trace_formula \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>_ _ : _" [90, 70, 70] 90) where
  "\<Gamma> \<turnstile>\<^sub>T \<S> : \<phi> = (\<forall>\<I>. (\<forall>(str, \<S>', \<phi>') \<in> set \<Gamma>. \<Turnstile>\<^sub>\<I> (\<S>', T):\<phi>') \<longrightarrow> \<Turnstile>\<^sub>\<I> (\<S>, T):\<phi>)"

lemma SKIP:
  shows "\<Gamma> \<turnstile>\<^sub>T SKIP : Rel Id"
  by (simp add: Id_def judgment_valid_def sequent_valid_def rec_sem_def)

lemma ASSIGN:
  shows "\<Gamma> \<turnstile>\<^sub>T (x := a) : Rel (Sb x a)"
  by (simp add: Sb_def judgment_valid_def sequent_valid_def rec_sem_def)

lemma SEQ:
  assumes "\<Gamma> \<turnstile>\<^sub>T \<S>\<^sub>1 : \<phi>\<^sub>1" and "\<Gamma> \<turnstile>\<^sub>T \<S>\<^sub>2 : \<phi>\<^sub>2"
  shows "\<Gamma> \<turnstile>\<^sub>T (\<S>\<^sub>1 ;; \<S>\<^sub>2) : (\<phi>\<^sub>1 \<Zcat> \<phi>\<^sub>2)"
  using assms
  apply (simp add: judgment_valid_def sequent_valid_def rec_sem_def)
  by blast

lemma IF:
  assumes "\<Gamma> \<turnstile>\<^sub>T (SKIP;;\<S>\<^sub>1) : (Pred (\<lambda>s. s \<Turnstile> (Not b)) \<squnion> \<phi>)"
    and "\<Gamma> \<turnstile>\<^sub>T (SKIP;;\<S>\<^sub>2) : (Pred (\<lambda>s. s \<Turnstile> b) \<squnion> \<phi>)"
  shows "\<Gamma> \<turnstile>\<^sub>T (IF b THEN \<S>\<^sub>1 ELSE \<S>\<^sub>2 FI) : \<phi>"
  using assms
  apply (simp add: judgment_valid_def sequent_valid_def rec_sem_def)
  by blast

lemma CONS:
  assumes "\<Gamma> \<turnstile>\<^sub>T \<S> : \<phi>'" and "[\<phi>'] \<turnstile> [\<phi>]"
  shows "\<Gamma> \<turnstile>\<^sub>T \<S> : \<phi>"
  using assms
  apply (simp add: judgment_valid_def sequent_valid_def Trace_Formula_Implication.sequent_valid_def)
  by blast

lemma UNFOLD:
  assumes "\<Gamma> \<turnstile>\<^sub>T \<S> : (\<phi>\<lbrakk>\<mu> X. \<phi> / X\<rbrakk>)"
    and "\<forall>X \<in> bound_vars \<phi>. X \<notin> free_vars \<phi>"
  shows "\<Gamma> \<turnstile>\<^sub>T \<S> : \<mu> X. \<phi>"
  using assms
  apply (simp add: judgment_valid_def sequent_valid_def)
  apply (intro allI impI subsetI InterI)
  apply (drule spec)
  apply (erule impE)
  apply assumption
  apply (drule_tac x="\<V>" in spec)
  apply (drule subsetD)
  apply assumption
  apply (subst (asm) \<mu>_unf[symmetric])
  apply assumption
  by simp

abbreviation subst_all where
  "subst_all \<Gamma> \<S> \<equiv> fold (\<lambda> (m, Y, \<phi>) Stm. subst_method_call Stm (SKIP;;Y) m) \<Gamma> \<S>"

lemma rfs_lift_subset_iff:
  "{(s, s # \<sigma>) | s \<sigma>. (s, \<sigma>) \<in> A} \<subseteq> {(s', s' # \<sigma>') | s' \<sigma>'. (s', \<sigma>') \<in> B} \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma subst_method_call_sem:
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S \<lbrakk>S' / m\<rbrakk>\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>(\<rho>(m := \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S'\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>))\<^sub>,\<^sub>\<I>"
proof (induction S)
  case (Call m')
  then show ?case by (cases "m' = m") simp_all
qed simp_all

primrec svars_S :: "S \<Rightarrow> stm_var set" where
  "svars_S SKIP = {}" |
  "svars_S (x := a) = {}" |
  "svars_S (S\<^sub>1;;S\<^sub>2) = svars_S S\<^sub>1 \<union> svars_S S\<^sub>2" |
  "svars_S (IF b THEN S\<^sub>1 ELSE S\<^sub>2 FI) = svars_S S\<^sub>1 \<union> svars_S S\<^sub>2" |
  "svars_S (Call m) = {}" |
  "svars_S (SVar sv) = {sv}"

lemma statement_semantics_svars_indep:
  "svars_S S = {} \<Longrightarrow> \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>'"
  by (induction S) auto

lemma bridge_that_gap:
  assumes "\<forall>\<I>. (\<forall>x\<in>set \<Gamma>'.
            case x of (str, Y, \<phi>) \<Rightarrow> \<forall>\<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>Y\<rbrakk>\<^sub>lfp (sem_ops T \<I>)\<^sub>,\<^sub>\<I> \<subseteq> \<lbrakk>\<phi>\<rbrakk>\<^sub>\<V>) \<longrightarrow>
        (\<forall>\<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>subst_all \<Gamma>' \<S>\<^sub>m\<rbrakk>\<^sub>lfp (sem_ops T \<I>)\<^sub>,\<^sub>\<I> \<subseteq> \<lbrakk>\<phi>\<^sub>m\<rbrakk>\<^sub>\<V>)"
  shows "\<forall>\<I> \<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>\<S>\<^sub>m\<rbrakk>\<^sub>lfp (sem_ops T \<I>)\<^sub>,\<^sub>\<I> \<subseteq> \<lbrakk>\<phi>\<^sub>m\<rbrakk>\<^sub>\<V>"
  using assms
  sorry

lemma CALL:
  assumes "fmlookup T m = Some \<S>\<^sub>m"
    and "\<forall>m' S'. fmlookup T m' = Some S' \<longrightarrow> svars_S S' = {}"
    and "(m, SVar Y\<^sub>m, \<phi>\<^sub>m) \<notin> set \<Gamma>"
    and "\<Gamma>' = (m, SVar Y\<^sub>m, \<phi>\<^sub>m) # \<Gamma>"
    and "\<Gamma>' \<turnstile>\<^sub>T (subst_all \<Gamma>' \<S>\<^sub>m) : \<phi>\<^sub>m"
  shows "\<Gamma> \<turnstile>\<^sub>T (Call m) : (Rel Id \<Zcat> \<phi>\<^sub>m)"
proof -
  have as1: "\<forall>\<I>. ((\<forall>(str, Y, \<phi>) \<in> set \<Gamma>'. \<Turnstile>\<^sub>\<I> (Y, T):\<phi>) \<longrightarrow> \<Turnstile>\<^sub>\<I> (subst_all \<Gamma>' \<S>\<^sub>m, T):\<phi>\<^sub>m)"
    using assms(5) by (simp add: sequent_valid_def)

  have as2: "\<forall>\<I>. ((\<forall>(str, Y, \<phi>) \<in> set \<Gamma>'. \<Turnstile>\<^sub>\<I> (SKIP;;Y, T):(Rel Id \<Zcat> \<phi>)) \<longrightarrow> \<Turnstile>\<^sub>\<I> (SKIP;;subst_all \<Gamma>' \<S>\<^sub>m, T):(Rel Id \<Zcat> \<phi>\<^sub>m))"
    using as1
    apply (simp add: Id_def)
    apply (simp add: judgment_valid_def)
    apply (simp only: rec_sem_def)
    by (simp add: rfs_lift_subset_iff)

  have as3: "\<forall>\<I> \<V>. (\<rho>\<^sub>0 T \<I>) m \<subseteq> \<lbrakk>Rel Id \<Zcat> \<phi>\<^sub>m\<rbrakk>\<^sub>\<V>"
    using as2
    apply (simp add: Id_def)
    apply (simp add: judgment_valid_def)
    apply (simp add: rec_sem_def)
    apply (simp add: initial_interpretation_def)
    apply (subst lfp_unfold[OF sem_ops_mono])
    apply (simp add: sem_ops_def)
    apply (simp add: assms(1))
    apply (simp add: rfs_lift_subset_iff)
    using bridge_that_gap
    by blast

  have as4: "\<forall>\<I> \<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>(Call m, T)\<rbrakk>\<^sub>\<I> \<subseteq> \<lbrakk>Rel Id \<Zcat> \<phi>\<^sub>m\<rbrakk>\<^sub>\<V>"
    using as3
    by (simp add: rec_sem_def)

  then show ?thesis
    by (simp add: Id_def sequent_valid_def judgment_valid_def rec_sem_def)
qed

end