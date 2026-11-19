theory Counterexample_CALL
  imports Judgment_Calculus
begin

text \<open>
  A counterexample to the lemmas @{text bridge_that_gap} and @{text CALL} in
  @{file "Judgment_Calculus.thy"}, for a non-empty antecedent \<open>\<Gamma>\<close>.

  Procedure table: \<open>T = {m {m1()}, m1 {skip}}\<close>; antecedent: \<open>\<Gamma> = Y_m1 : false\<close>.
  All premises of @{text CALL} hold, so it yields \<open>\<Gamma> \<turnstile>\<^sub>T m() : Id \<Zcat> Id \<Zcat> false\<close>.
  This sequent is not valid: the formula denotes the empty set, but \<open>\<Gamma>\<close> is
  satisfied by the interpretation that maps \<open>Y_m1\<close> to \<open>{}\<close>, and \<open>m()\<close> still
  has traces under it.

  The reason is a mismatch in how procedures are interpreted. In the premise
  of @{text CALL}, @{text subst_all} replaces the call \<open>m1()\<close> by \<open>skip; Y_m1\<close>,
  since \<open>m1\<close> occurs in \<open>\<Gamma>\<close>. Validity of sequents, however, interprets \<open>m1\<close> by
  the least fixed point of @{const sem_ops}, which the interpretation of \<open>Y_m1\<close>
  does not constrain. The premise of @{text CALL} thus says nothing about the
  traces of \<open>m1()\<close>.

  The lemmas below that check the premises and refute the conclusions do not
  use @{text bridge_that_gap} or @{text CALL}.
\<close>

abbreviation false_tf :: trace_formula where
  "false_tf \<equiv> Pred (\<lambda>_. False)"

lemma Id_chop_false_empty: "\<lbrakk>Rel Id \<Zcat> false_tf\<rbrakk>\<^sub>\<V> = {}"
  by (auto simp: Id_def)

lemma Id_chop_Id_chop_false_empty: "\<lbrakk>Rel Id \<Zcat> Rel Id \<Zcat> false_tf\<rbrakk>\<^sub>\<V> = {}"
  by (auto simp: Id_def)

section \<open>The statement of bridge_that_gap is false\<close>

definition T\<^sub>1 :: "(method_name, S) fmap" where
  "T\<^sub>1 = fmap_of_list [(''m1'', SKIP)]"

lemma m1_trace: "(s, [s, s]) \<in> lfp (sem_ops T\<^sub>1 \<I>) ''m1''"
  by (subst lfp_unfold[OF sem_ops_mono]) (simp add: sem_ops_def T\<^sub>1_def)

lemma bridge_that_gap_assumption:
  "\<forall>\<I>. (\<forall>x\<in>set [(''m1'', SVar ''Y_m1'', false_tf)].
          case x of (str, Y, \<phi>) \<Rightarrow> \<forall>\<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>Y\<rbrakk>\<^sub>lfp (sem_ops T\<^sub>1 \<I>)\<^sub>,\<^sub>\<I> \<subseteq> \<lbrakk>\<phi>\<rbrakk>\<^sub>\<V>) \<longrightarrow>
        (\<forall>\<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>subst_all [(''m1'', SVar ''Y_m1'', false_tf)] (Call ''m1'')\<rbrakk>\<^sub>lfp (sem_ops T\<^sub>1 \<I>)\<^sub>,\<^sub>\<I>
              \<subseteq> \<lbrakk>Rel Id \<Zcat> false_tf\<rbrakk>\<^sub>\<V>)"
  by auto

lemma bridge_that_gap_conclusion_false:
  "\<not> (\<forall>\<I> \<V>. \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>Call ''m1''\<rbrakk>\<^sub>lfp (sem_ops T\<^sub>1 \<I>)\<^sub>,\<^sub>\<I> \<subseteq> \<lbrakk>Rel Id \<Zcat> false_tf\<rbrakk>\<^sub>\<V>)"
  using m1_trace Id_chop_false_empty by fastforce

text \<open>With the unproven lemma, this yields a contradiction.\<close>

lemma bridge_that_gap_derives_False: False
  using bridge_that_gap[OF bridge_that_gap_assumption] bridge_that_gap_conclusion_false
  by blast

section \<open>The rule CALL is unsound\<close>

definition T\<^sub>2 :: "(method_name, S) fmap" where
  "T\<^sub>2 = fmap_of_list [(''m'', Call ''m1''), (''m1'', SKIP)]"

definition \<Gamma>\<^sub>2 :: "(string \<times> S \<times> trace_formula) list" where
  "\<Gamma>\<^sub>2 = [(''m1'', SVar ''Y_m1'', false_tf)]"

definition \<Gamma>\<^sub>2' :: "(string \<times> S \<times> trace_formula) list" where
  "\<Gamma>\<^sub>2' = (''m'', SVar ''Y_m'', Rel Id \<Zcat> false_tf) # \<Gamma>\<^sub>2"

lemma CALL_premise_1: "fmlookup T\<^sub>2 ''m'' = Some (Call ''m1'')"
  by (simp add: T\<^sub>2_def)

lemma CALL_premise_2: "\<forall>m' S'. fmlookup T\<^sub>2 m' = Some S' \<longrightarrow> svars_S S' = {}"
  by (simp add: T\<^sub>2_def)

lemma CALL_premise_3: "(''m'', SVar ''Y_m'', Rel Id \<Zcat> false_tf) \<notin> set \<Gamma>\<^sub>2"
  by (simp add: \<Gamma>\<^sub>2_def)

text \<open>@{text subst_all} turns the body \<open>m1()\<close> into \<open>skip; Y_m1\<close>, which has no
  traces when \<open>Y_m1 : false\<close> holds.\<close>

lemma CALL_premise_5: "\<Gamma>\<^sub>2' \<turnstile>\<^sub>T\<^sub>2 (subst_all \<Gamma>\<^sub>2' (Call ''m1'')) : (Rel Id \<Zcat> false_tf)"
  by (auto simp: sequent_valid_def judgment_valid_def rec_sem_def \<Gamma>\<^sub>2'_def \<Gamma>\<^sub>2_def Id_def)

lemma m_trace: "(s, [s, s, s]) \<in> lfp (sem_ops T\<^sub>2 \<I>) ''m''"
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def T\<^sub>2_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  by (simp add: sem_ops_def)

lemma CALL_conclusion_invalid: "\<not> \<Gamma>\<^sub>2 \<turnstile>\<^sub>T\<^sub>2 (Call ''m'') : (Rel Id \<Zcat> Rel Id \<Zcat> false_tf)"
proof
  assume "\<Gamma>\<^sub>2 \<turnstile>\<^sub>T\<^sub>2 (Call ''m'') : (Rel Id \<Zcat> Rel Id \<Zcat> false_tf)"
  then have "\<Turnstile>\<^sub>(\<lambda>_. {}) (Call ''m'', T\<^sub>2):(Rel Id \<Zcat> Rel Id \<Zcat> false_tf)"
    by (simp add: sequent_valid_def judgment_valid_def rec_sem_def \<Gamma>\<^sub>2_def)
  then have "lfp (sem_ops T\<^sub>2 (\<lambda>_. {})) ''m'' = {}"
    by (simp add: judgment_valid_def rec_sem_def initial_interpretation_def
                  Id_chop_Id_chop_false_empty)
  then show False
    using m_trace by blast
qed

text \<open>With the unproven rule, this yields a contradiction.\<close>

lemma CALL_derives_False: False
  using CALL[OF CALL_premise_1 CALL_premise_2 CALL_premise_3 \<Gamma>\<^sub>2'_def
                CALL_premise_5]
        CALL_conclusion_invalid
  by simp

end
