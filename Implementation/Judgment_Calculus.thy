theory Judgment_Calculus
  imports "Rec_Semantics" "Trace_Formula_Implication"
begin

definition judgment_valid ::
    "(stm_var \<Rightarrow> trace set) \<Rightarrow> Rec \<Rightarrow> trace_formula \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>_ _:_" [70, 70, 70] 70) where
  "\<Turnstile>\<^sub>\<I> \<S>:\<phi> = (\<forall>\<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>\<S>\<rbrakk>\<^sub>\<I> \<subseteq> \<lbrakk>\<phi>\<rbrakk>\<^sub>\<V>)"

text \<open>In the conclusion of a sequent, each method \<open>m\<close> with an antecedent
  \<open>(m, Y, \<phi>)\<close> in \<open>\<Gamma>\<close> is interpreted as its continuation: its body in the
  procedure table is replaced by \<open>Y\<close>. This matches rule CALL, which replaces
  the calls of \<open>m\<close> by \<open>SKIP;;Y\<close>. For \<open>\<Gamma> = []\<close>, the table is unchanged.\<close>

definition override ::
    "(string \<times> S \<times> trace_formula) list \<Rightarrow> (method_name, S) fmap \<Rightarrow> (method_name, S) fmap" where
  "override \<Gamma> T = T ++\<^sub>f fmap_of_list (map (\<lambda>(m, Y, \<phi>). (m, Y)) \<Gamma>)"

definition sequent_valid ::
    "(string \<times> S \<times> trace_formula) list \<Rightarrow> (method_name, S) fmap \<Rightarrow>
      S \<Rightarrow> trace_formula \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>_ _ : _" [90, 70, 70] 90) where
  "\<Gamma> \<turnstile>\<^sub>T \<S> : \<phi> = (\<forall>\<I>. (\<forall>(str, \<S>', \<phi>') \<in> set \<Gamma>. \<Turnstile>\<^sub>\<I> (\<S>', T):\<phi>') \<longrightarrow> \<Turnstile>\<^sub>\<I> (\<S>, override \<Gamma> T):\<phi>)"

lemma override_Nil [simp]: "override [] T = T"
  by (simp add: override_def)

text \<open>A statement variable does not depend on the procedure table.\<close>

lemma judgment_valid_SVar [simp]: "\<Turnstile>\<^sub>\<I> (SVar Y, T):\<phi> = (\<forall>\<V>. \<I> Y \<subseteq> \<lbrakk>\<phi>\<rbrakk>\<^sub>\<V>)"
  by (simp add: judgment_valid_def rec_sem_def)

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

lemma statement_semantics_svars_agree:
  "\<forall>sv \<in> svars_S S. \<I> sv = \<I>' sv \<Longrightarrow> \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>'"
  by (induction S) auto

lemma sem_ops_svars_indep:
  assumes "\<forall>m' S'. fmlookup T m' = Some S' \<longrightarrow> svars_S S' = {}"
  shows "sem_ops T \<I> = sem_ops T \<I>'"
proof (intro ext)
  fix \<rho> m
  show "sem_ops T \<I> \<rho> m = sem_ops T \<I>' \<rho> m"
  proof (cases "fmlookup T m")
    case (Some S')
    then have "svars_S S' = {}"
      using assms by blast
    then show ?thesis
      using Some statement_semantics_svars_indep[of S' \<rho> \<I> \<I>'] by (simp add: sem_ops_def)
  qed (simp add: sem_ops_def)
qed

lemma SKIP_Seq_sem: "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>SKIP;;S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<sharp>\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>"
  by auto

lemma subst_all_sem:
  assumes "\<forall>(n, Y, \<psi>) \<in> set \<Gamma>. \<rho> n = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>SKIP;;Y\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>"
  shows "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>subst_all \<Gamma> S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>"
  using assms
proof (induction \<Gamma> arbitrary: S)
  case (Cons x \<Gamma>)
  obtain n Y \<psi> where x: "x = (n, Y, \<psi>)"
    by (cases x) auto
  have "\<rho> n = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>SKIP;;Y\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>"
    using Cons.prems x by simp
  then have "\<rho>(n := \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>SKIP;;Y\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>) = \<rho>"
    by (rule fun_upd_idem)
  then show ?case
    using Cons subst_method_call_sem[of S "SKIP;;Y" n \<rho> \<I>] x by simp
qed simp

lemma fmlookup_override_Cons:
  "fmlookup (override ((m, Y, \<phi>) # \<Gamma>) T) n =
    (if n = m then Some Y else fmlookup (override \<Gamma> T) n)"
  by (simp add: override_def fmlookup_of_list)

lemma fmlookup_override_notin:
  "n \<notin> fst ` set \<Gamma> \<Longrightarrow> fmlookup (override \<Gamma> T) n = fmlookup T n"
  by (induction \<Gamma>) (auto simp: fmlookup_override_Cons)

lemma fmlookup_override_in:
  "distinct (map fst \<Gamma>) \<Longrightarrow> (n, Y, \<psi>) \<in> set \<Gamma> \<Longrightarrow> fmlookup (override \<Gamma> T) n = Some Y"
proof (induction \<Gamma>)
  case (Cons x \<Gamma>)
  obtain n' Y' \<psi>' where x: "x = (n', Y', \<psi>')"
    by (cases x) auto
  show ?case
  proof (cases "n = n'")
    case True
    then have "(n, Y, \<psi>) = x"
      using Cons.prems x by (auto simp: image_iff)
    then show ?thesis
      using x by (simp add: fmlookup_override_Cons)
  next
    case False
    then show ?thesis
      using Cons x by (simp add: fmlookup_override_Cons)
  qed
qed simp

lemma fmlookup_override_Some:
  "fmlookup (override \<Gamma> T) n = Some S' \<Longrightarrow> (\<exists>\<psi>. (n, S', \<psi>) \<in> set \<Gamma>) \<or> fmlookup T n = Some S'"
  by (induction \<Gamma>) (auto simp: fmlookup_override_Cons split: if_splits)

text \<open>Fixed-point induction for rule CALL: if the body of \<open>m\<close> stays within \<open>g\<close>
  when \<open>m\<close> is interpreted as \<open>SKIP;;Y\<^sub>m\<close> with \<open>Y\<^sub>m\<close> mapped to \<open>g\<close>, then every
  trace of \<open>m\<close> is in \<open>\<sharp>g\<close>.\<close>

lemma bridge_that_gap:
  assumes "fmlookup T m = Some \<S>\<^sub>m"
    and "\<forall>m' S'. fmlookup T m' = Some S' \<longrightarrow> svars_S S' = {}"
    and "m \<notin> fst ` set \<Gamma>"
    and "\<forall>(n, S', \<psi>) \<in> set \<Gamma>. Y\<^sub>m \<notin> svars_S S'"
    and "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>\<S>\<^sub>m\<rbrakk>\<^sub>lfp (sem_ops (override ((m, SVar Y\<^sub>m, \<phi>\<^sub>m) # \<Gamma>) T) (\<I>(Y\<^sub>m := g)))\<^sub>,\<^sub>\<I>(Y\<^sub>m := g) \<subseteq> g"
  shows "lfp (sem_ops (override \<Gamma> T) \<I>) m \<subseteq> \<sharp>g"
proof -
  let ?T' = "override ((m, SVar Y\<^sub>m, \<phi>\<^sub>m) # \<Gamma>) T"
  let ?\<I>' = "\<I>(Y\<^sub>m := g)"
  let ?r = "lfp (sem_ops ?T' ?\<I>')"
  have r: "?r n = sem_ops ?T' ?\<I>' ?r n" for n
    by (rule fun_cong[OF lfp_unfold[OF sem_ops_mono]])
  have rm: "?r m = \<sharp>g"
  proof -
    have "?r m = sem_ops ?T' ?\<I>' ?r m"
      by (rule r)
    also have "\<dots> = \<sharp>g"
      by (simp add: sem_ops_def fmlookup_override_Cons)
    finally show ?thesis .
  qed
  have "sem_ops (override \<Gamma> T) \<I> ?r n \<subseteq> ?r n" for n
  proof (cases "n = m")
    case True
    have "svars_S \<S>\<^sub>m = {}"
      using assms(1,2) by blast
    then have "statement_semantics \<S>\<^sub>m ?r \<I> = statement_semantics \<S>\<^sub>m ?r ?\<I>'"
      by (rule statement_semantics_svars_indep)
    then have "statement_semantics \<S>\<^sub>m ?r \<I> \<subseteq> g"
      using assms(5) by simp
    moreover have "sem_ops (override \<Gamma> T) \<I> ?r m = \<sharp>statement_semantics \<S>\<^sub>m ?r \<I>"
      using assms(1,3) by (simp add: sem_ops_def fmlookup_override_notin)
    ultimately show ?thesis
      using True rm by auto
  next
    case False
    have "statement_semantics S' ?r \<I> = statement_semantics S' ?r ?\<I>'"
      if "fmlookup (override \<Gamma> T) n = Some S'" for S'
    proof (rule statement_semantics_svars_agree)
      from fmlookup_override_Some[OF that] have "Y\<^sub>m \<notin> svars_S S'"
      proof
        assume "\<exists>\<psi>. (n, S', \<psi>) \<in> set \<Gamma>"
        then obtain \<psi> where "(n, S', \<psi>) \<in> set \<Gamma>"
          by blast
        with assms(4) show ?thesis
          by (auto dest!: bspec)
      next
        assume "fmlookup T n = Some S'"
        with assms(2) have "svars_S S' = {}"
          by blast
        then show ?thesis
          by simp
      qed
      then show "\<forall>sv \<in> svars_S S'. \<I> sv = ?\<I>' sv"
        by auto
    qed
    then have "sem_ops (override \<Gamma> T) \<I> ?r n = sem_ops ?T' ?\<I>' ?r n"
      using False by (auto simp: sem_ops_def fmlookup_override_Cons split: option.splits)
    then show ?thesis
      by (subst r) simp
  qed
  then have "lfp (sem_ops (override \<Gamma> T) \<I>) \<le> ?r"
    by (intro lfp_lowerbound) (simp add: le_fun_def)
  then have "lfp (sem_ops (override \<Gamma> T) \<I>) m \<subseteq> ?r m"
    by (rule le_funD)
  with rm show ?thesis
    by simp
qed

lemma CALL:
  assumes "fmlookup T m = Some \<S>\<^sub>m"
    and "\<forall>m' S'. fmlookup T m' = Some S' \<longrightarrow> svars_S S' = {}"
    and "m \<notin> fst ` set \<Gamma>"
    and "distinct (map fst \<Gamma>)"
    and "\<forall>(n, S', \<psi>) \<in> set \<Gamma>. Y\<^sub>m \<notin> svars_S S'"
    and "\<Gamma>' = (m, SVar Y\<^sub>m, \<phi>\<^sub>m) # \<Gamma>"
    and "\<Gamma>' \<turnstile>\<^sub>T (subst_all \<Gamma>' \<S>\<^sub>m) : \<phi>\<^sub>m"
  shows "\<Gamma> \<turnstile>\<^sub>T (Call m) : (Rel Id \<Zcat> \<phi>\<^sub>m)"
  unfolding sequent_valid_def
proof (intro allI impI)
  fix \<I>
  assume \<Gamma>: "\<forall>(str, \<S>', \<phi>') \<in> set \<Gamma>. \<Turnstile>\<^sub>\<I> (\<S>', T):\<phi>'"
  define g where "g = (\<Inter>\<V>. \<lbrakk>\<phi>\<^sub>m\<rbrakk>\<^sub>\<V>)"
  let ?\<I>' = "\<I>(Y\<^sub>m := g)"
  let ?r = "lfp (sem_ops (override \<Gamma>' T) ?\<I>')"

  text \<open>The antecedents \<open>\<Gamma>'\<close> hold when \<open>Y\<^sub>m\<close> is interpreted as \<open>g\<close>.\<close>
  have \<rho>\<^sub>0: "lfp (sem_ops T ?\<I>') = lfp (sem_ops T \<I>)"
    using sem_ops_svars_indep[OF assms(2), of ?\<I>' \<I>] by simp
  have \<Gamma>': "judgment_valid ?\<I>' (\<S>', T) \<phi>'" if "(str, \<S>', \<phi>') \<in> set \<Gamma>'" for str \<S>' \<phi>'
  proof (cases "(str, \<S>', \<phi>') \<in> set \<Gamma>")
    case True
    from assms(5) True have "Y\<^sub>m \<notin> svars_S \<S>'"
      by (auto dest!: bspec)
    then have "statement_semantics \<S>' \<rho> ?\<I>' = statement_semantics \<S>' \<rho> \<I>" for \<rho>
      by (intro statement_semantics_svars_agree) auto
    moreover from \<Gamma> True have "judgment_valid \<I> (\<S>', T) \<phi>'"
      by (auto dest!: bspec)
    ultimately show ?thesis
      using \<rho>\<^sub>0 by (simp add: judgment_valid_def rec_sem_def initial_interpretation_def)
  next
    case False
    then show ?thesis
      using that assms(6) by (auto simp: judgment_valid_def rec_sem_def g_def)
  qed
  then have "\<forall>(str, \<S>', \<phi>') \<in> set \<Gamma>'. judgment_valid ?\<I>' (\<S>', T) \<phi>'"
    by auto
  moreover from assms(7) have "(\<forall>(str, \<S>', \<phi>') \<in> set \<Gamma>'. judgment_valid ?\<I>' (\<S>', T) \<phi>') \<longrightarrow>
      judgment_valid ?\<I>' (subst_all \<Gamma>' \<S>\<^sub>m, override \<Gamma>' T) \<phi>\<^sub>m"
    unfolding sequent_valid_def by (rule spec)
  ultimately have "judgment_valid ?\<I>' (subst_all \<Gamma>' \<S>\<^sub>m, override \<Gamma>' T) \<phi>\<^sub>m"
    by (rule rev_mp)
  then have subst_sub: "statement_semantics (subst_all \<Gamma>' \<S>\<^sub>m) ?r ?\<I>' \<subseteq> g"
    by (auto simp: judgment_valid_def rec_sem_def initial_interpretation_def g_def)

  text \<open>Replacing the calls by their continuations does not change the semantics.\<close>
  have cont: "?r n = statement_semantics (SKIP;;Y) ?r ?\<I>'" if "(n, Y, \<psi>) \<in> set \<Gamma>'" for n Y \<psi>
  proof -
    have "distinct (map fst \<Gamma>')"
      using assms(3,4,6) by auto
    then have lookup: "fmlookup (override \<Gamma>' T) n = Some Y"
      using that by (rule fmlookup_override_in)
    have "?r n = sem_ops (override \<Gamma>' T) ?\<I>' ?r n"
      by (rule fun_cong[OF lfp_unfold[OF sem_ops_mono]])
    also have "\<dots> = statement_semantics (SKIP;;Y) ?r ?\<I>'"
      using lookup by (simp only: sem_ops_def SKIP_Seq_sem option.case)
    finally show ?thesis .
  qed
  have "\<forall>(n, Y, \<psi>) \<in> set \<Gamma>'. ?r n = statement_semantics (SKIP;;Y) ?r ?\<I>'"
  proof (intro ballI case_prodI2)
    fix x n p Y \<psi>
    assume "x \<in> set \<Gamma>'" "x = (n, p)" "p = (Y, \<psi>)"
    then have "(n, Y, \<psi>) \<in> set \<Gamma>'"
      by simp
    then show "?r n = statement_semantics (SKIP;;Y) ?r ?\<I>'"
      by (rule cont)
  qed
  then have "statement_semantics (subst_all \<Gamma>' \<S>\<^sub>m) ?r ?\<I>' = statement_semantics \<S>\<^sub>m ?r ?\<I>'"
    by (rule subst_all_sem)
  then have "lfp (sem_ops (override \<Gamma> T) \<I>) m \<subseteq> \<sharp>g"
    using bridge_that_gap[OF assms(1,2,3,5)] subst_sub assms(6) by simp
  moreover have "\<sharp>g \<subseteq> \<lbrakk>Rel Id \<Zcat> \<phi>\<^sub>m\<rbrakk>\<^sub>\<V>" for \<V>
    by (auto simp: Id_def g_def)
  ultimately show "\<Turnstile>\<^sub>\<I> (Call m, override \<Gamma> T):(Rel Id \<Zcat> \<phi>\<^sub>m)"
    by (simp add: judgment_valid_def rec_sem_def initial_interpretation_def) (meson order_trans)
qed

end