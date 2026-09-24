theory TFI_Prover
  imports Trace_Formula_Implication "HOL-Eisbach.Eisbach"
begin

method close = rule CLOSE, simp; fail
method false = rule FALSE, simp; fail
method true = rule TRUE, simp; fail

method disj_l = rule DISJ_L, fastforce; simp
method disj_r = rule DISJ_R, fastforce, simp
method conj_l = rule CONJ_L, fastforce, simp
method conj_r = rule CONJ_R, fastforce; simp

method ch_predl = rule CH_PREDL, fastforce
method ch_predr = rule CH_PREDR, fastforce, simp, simp

method end_id = rule END_ID, simp, simp; simp
method end_upd = rule END_UPD, simp, simp; simp

method ch_ch_l = rule CH_CH_L, simp, simp
method ch_ch_r = rule CH_CH_R, simp, simp

method ch_disj_l = rule CH_DISJ_L, fastforce; simp
method ch_disj_r = rule CH_DISJ_R, fastforce, simp
method ch_conj_l = rule CH_CONJ_L, fastforce, simp

method arb1 = rule ARB1, simp, simp
method arb2 = rule ARB2, fastforce, simp, simp

method unfl = rule UNFL, simp, simp, simp
method unfr = rule UNFR, simp, simp, simp

method ch_unfl = rule CH_UNFL, simp, simp, simp
method ch_unfr = rule CH_UNFR, simp, simp, simp

method tfi_case for p :: "state \<Rightarrow> bool" = rule CASE[of _ p]
method pred for p :: "state \<Rightarrow> bool" = rule PRED[of _ p], fastforce

named_theorems rels

declare Id_def [rels]
declare Sb_def [rels]

method rel declares rels = rule REL, simp, simp, (fastforce simp add: rels); fail

lemma CH_REL_take: 
  assumes "\<Delta> = \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>1' # \<Delta>'"
    and "\<Psi>s = \<Psi>\<^sub>1' # \<Psi>s'"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> [\<Psi>\<^sub>1]"
    and "\<forall>\<Psi>' \<in> set \<Psi>s'. \<exists>\<Psi>. \<Psi> \<Zcat> \<Psi>' \<in> set \<Delta>' \<and> \<xi> \<diamondop> \<Gamma> \<turnstile> [\<Psi>]"
  shows "\<forall>\<Psi>' \<in> set \<Psi>s. \<exists>\<Psi>. \<Psi> \<Zcat> \<Psi>' \<in> set \<Delta> \<and> \<xi> \<diamondop> \<Gamma> \<turnstile> [\<Psi>]"
  using assms by auto

lemma CH_REL_drop: 
  assumes "\<Delta> = \<Psi> # \<Delta>'"
    and "\<forall>\<Psi>' \<in> set \<Psi>s. \<exists>\<Psi>. \<Psi> \<Zcat> \<Psi>' \<in> set \<Delta>' \<and> \<xi> \<diamondop> \<Gamma> \<turnstile> [\<Psi>]"
  shows "\<forall>\<Psi>' \<in> set \<Psi>s. \<exists>\<Psi>. \<Psi> \<Zcat> \<Psi>' \<in> set \<Delta> \<and> \<xi> \<diamondop> \<Gamma> \<turnstile> [\<Psi>]"
  using assms by auto

method ch_rel_take methods m = rule CH_REL_take, simp, simp, (m; fail)
method ch_rel_drop = rule CH_REL_drop, (simp; fail)

method ch_id methods m = 
  rule CH_ID, simp, (ch_rel_take m | ch_rel_drop)+, simp, simp
method ch_upd methods m = 
  rule CH_UPD, simp, (ch_rel_take m | ch_rel_drop)+, simp, simp

method lenl for i :: nat = 
  rule LENL[of _ _ _ i], simp, simp, simp, simp add: eval_nat_numeral
method lenr for i :: nat = 
  rule LENR[of _ _ _ i], simp, simp, simp, simp add: eval_nat_numeral
method ch_lenl for i :: nat = 
  rule CH_LENL[of _ _ _ _ i], simp, simp, simp, simp add: eval_nat_numeral
method ch_lenr for i :: nat = 
  rule CH_LENR[of _ _ _ _ i], simp, simp, simp, simp add: eval_nat_numeral

method rvar = rule RVAR, simp, simp, simp; auto

method fpi for inv :: "state \<Rightarrow> bool" = 
  rule FPI[of _ _ _ _ _ _ _ inv], simp, simp, simp, simp, simp, fastforce
method fpi_alt for inv :: "state \<Rightarrow> bool" = 
  rule FPI_ALT[of _ _ _ _ _ _ inv], simp, simp, simp, simp, fastforce

lemma NOT_R:
  assumes "Pred p \<in> set \<Delta>"
    and "\<xi> \<diamondop> Pred (\<lambda>s. \<not> p s) # \<Gamma> \<turnstile> remove1 (Pred p) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
  apply (rule CASE[of _ p])
  apply (rule CLOSE, simp add: assms)
  apply (rule sequent_validI)
  using sequent_validD[OF assms(2)] disj_ins_rem[OF assms(1)] by (auto 7 2)

method not_r = rule NOT_R, fastforce, simp

lemma UNFR_no_fixpoint_l: "\<lbrakk>\<mu> X. \<Psi> \<in> set \<Delta>; \<mu> X'. \<Phi> \<notin> set \<Gamma>;
              \<forall>X\<^sub>1 \<in> bound_vars \<Psi>. X\<^sub>1 \<notin> free_vars \<Psi>;
            \<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<lbrakk>\<mu> X. \<Psi> / X\<rbrakk> # remove1 (\<mu> X. \<Psi>) \<Delta>\<rbrakk> \<Longrightarrow> \<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
  by (rule UNFR)

method unfr_no_fixpoint_l = rule UNFR_no_fixpoint_l, fastforce, simp, simp, simp

method tfi_close_proof = close | true | false | rel | rvar
method tfi_simp = (conj_l | disj_r | ch_conj_l | ch_disj_r | ch_predr | 
                   ch_unfl | ch_unfr | ch_ch_r | ch_ch_l)+
method tfi_split = disj_l | conj_r | ch_disj_l
method tfi_rel = end_id | end_upd | ch_id tfi_close_proof | ch_upd tfi_close_proof
method tfi_arb methods m = arb1, m; fail | arb2
method tfi_auto = (tfi_close_proof | tfi_simp | not_r | tfi_split | 
                   unfr_no_fixpoint_l | tfi_arb tfi_auto | tfi_rel)+
method tfi_unf = (tfi_auto | unfr | unfl)+

end