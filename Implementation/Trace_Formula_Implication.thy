theory Trace_Formula_Implication
  imports Trace_Formulas
begin

type_synonym rvar_assumption_set = "(string \<times> (state \<Rightarrow> bool) \<times> trace_formula) set"

fun assumption_valid ::
    "rvar_assumption_set \<Rightarrow> (var, trace set) fmap \<Rightarrow> bool" where
  "assumption_valid \<xi> \<V> = (\<forall>(X\<^sub>1, p, \<Psi>) \<in> \<xi>. \<lbrakk>RVar X\<^sub>1 \<sqinter> Pred p\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>)"

primrec conj :: "trace_formula list \<Rightarrow> trace_formula" ("\<And> _" [60] 60) where
  "\<And> [] = Pred (\<lambda>_. True)" |
  "\<And> \<Phi> # \<Gamma> = \<Phi> \<sqinter> (\<And> \<Gamma>)"

primrec disj ::  "trace_formula list \<Rightarrow> trace_formula" ("\<Or> _" [60] 60) where
  "\<Or> [] = Pred (\<lambda>_. False)" |
  "\<Or> \<Psi> # \<Gamma> = \<Psi> \<squnion> (\<Or> \<Gamma>)"

lemma conj_ins_rem:
  assumes "\<Phi> \<in> set \<Gamma>"
  shows "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> \<Phi> # remove1 \<Phi> \<Gamma>\<rbrakk>\<^sub>\<V>"
  using assms by (induction \<Gamma>, auto)

lemma disj_ins_rem:
  assumes "\<Psi> \<in> set \<Delta>"
  shows "\<lbrakk>\<Or> \<Psi> # remove1 \<Psi> \<Delta>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>"
  using assms by (induction \<Delta>, auto)

lemma subset_\<Phi>:
  assumes "\<Phi> \<in> set \<Gamma>"
  shows "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>"
  using conj_ins_rem[OF assms] by auto

lemma subset_\<Psi>:
  assumes "\<Psi> \<in> set \<Delta>"
  shows "\<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>"
  using disj_ins_rem[OF assms] by auto

definition sequent_valid :: 
    "rvar_assumption_set \<Rightarrow> trace_formula list \<Rightarrow> trace_formula list \<Rightarrow> bool" 
    ("_ \<diamondop> _ \<turnstile> _" [60, 60, 60] 60) where
  "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta> = (\<forall>\<V>. assumption_valid \<xi> \<V> \<longrightarrow> \<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>)"

abbreviation sequent_valid_empty_assumption :: 
    "trace_formula list \<Rightarrow> trace_formula list \<Rightarrow> bool" ("_ \<turnstile> _" [60, 60] 60) where
  "\<Gamma> \<turnstile> \<Delta> \<equiv> {} \<diamondop> \<Gamma> \<turnstile> \<Delta>"

lemma sequent_validI:
  assumes "\<And>\<V>. assumption_valid \<xi> \<V> \<Longrightarrow> \<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
  using assms sequent_valid_def by auto

lemma sequent_validD:
  assumes "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
    and "assumption_valid \<xi> \<V>"
  shows "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>"
  using assms sequent_valid_def by auto

lemma CLOSE: 
  assumes "\<exists>\<Phi> \<in> set \<Gamma>. \<Phi> \<in> set \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  obtain \<Phi> where 1: "\<Phi> \<in> set \<Gamma>" and 2: "\<Phi> \<in> set \<Delta>" using assms by auto
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>" by (rule subset_\<Phi>[OF 1])
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule subset_\<Psi>[OF 2])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma FALSE:
  assumes "Pred (\<lambda>s. False) \<in> set \<Gamma>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>Pred (\<lambda>s. False)\<rbrakk>\<^sub>\<V>" using conj_ins_rem[OF assms] by auto
  also have "... = {}" by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma TRUE:
  assumes "Pred (\<lambda>s. True) \<in> set \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> UNIV" by auto
  also have "... = \<lbrakk>Pred (\<lambda>s. True)\<rbrakk>\<^sub>\<V>" by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF assms] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma DISJ_L:
  assumes "\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2 \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Phi>\<^sub>1 # remove1 (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Gamma> \<turnstile> \<Delta>"
    and "\<xi> \<diamondop> \<Phi>\<^sub>2 # remove1 (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> \<Phi>\<^sub>1 # ?\<Gamma>\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<And> \<Phi>\<^sub>2 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using assms(2,3) asm_valid sequent_validD by blast
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed
  
lemma DISJ_R:
  assumes "\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2 \<in> set \<Delta>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<^sub>1 # \<Psi>\<^sub>2 # remove1 (\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2) \<Delta>"
  fix \<V>
  assume "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Psi>\<^sub>1 # \<Psi>\<^sub>2 # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(2)])
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using disj_ins_rem[OF assms(1)] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CONJ_L:
  assumes "\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2 \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Phi>\<^sub>1 # \<Phi>\<^sub>2 # remove1 (\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 (\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> \<Phi>\<^sub>1 # \<Phi>\<^sub>2 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" using conj_ins_rem[OF assms(1)] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(2) asm_valid])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CONJ_R: 
  assumes "\<Psi>\<^sub>1 \<sqinter> \<Psi>\<^sub>2 \<in> set \<Delta>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<^sub>1 # remove1 (\<Psi>\<^sub>1 \<sqinter> \<Psi>\<^sub>2) \<Delta>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<^sub>2 # remove1 (\<Psi>\<^sub>1 \<sqinter> \<Psi>\<^sub>2) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (\<Psi>\<^sub>1 \<sqinter> \<Psi>\<^sub>2) \<Delta>"
  fix \<V>
  assume "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Psi>\<^sub>1 # ?\<Delta>\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Or> \<Psi>\<^sub>2 # ?\<Delta>\<rbrakk>\<^sub>\<V>" using sequent_validD assms(2,3) by blast
  also have "... = \<lbrakk>\<Or> (\<Psi>\<^sub>1 \<sqinter> \<Psi>\<^sub>2) # ?\<Delta>\<rbrakk>\<^sub>\<V>" by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

fun current_state :: "trace_formula list \<Rightarrow> trace_formula list" where
  "current_state \<Gamma> = filter (\<lambda>\<Phi>. case \<Phi> of Pred p \<Rightarrow> True | _ \<Rightarrow> False) \<Gamma>"

lemma subset_P\<^sub>\<Gamma>: "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V>"
  by (induction \<Gamma>, auto)

lemma subset_\<Phi>_P\<^sub>\<Gamma>:
  assumes "\<Phi> \<in> set \<Gamma>"
  shows "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> \<Phi> # current_state \<Gamma>\<rbrakk>\<^sub>\<V>"
  using subset_\<Phi>[OF assms] subset_P\<^sub>\<Gamma> by auto

lemma P\<^sub>\<Gamma>_head_only:
  assumes "(s, \<sigma>) \<in> \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V>"
  shows "(s, \<sigma>') \<in> \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V>"
  using assms
proof (induction \<Gamma>)
  case (Cons \<Phi> \<Gamma>)
  thus ?case by (cases \<Phi>, auto)
qed simp

lemma CASE:
  assumes "\<xi> \<diamondop> Pred p # \<Gamma> \<turnstile> \<Delta>"
    and "\<xi> \<diamondop> Pred (\<lambda>s. \<not> p s) # \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence 1: "\<lbrakk>\<And> Pred p # \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(1)])
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> Pred p # \<Gamma>\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<And> Pred (\<lambda>s. \<not> p s) # \<Gamma>\<rbrakk>\<^sub>\<V>" by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using 1 sequent_validD[OF assms(2) asm_valid] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma PRED:
  assumes "\<And>\<V>. \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>Pred q\<rbrakk>\<^sub>\<V>"
    and "\<xi> \<diamondop> Pred q # \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V>" by (induction \<Gamma>, auto)
  also have "... \<subseteq> \<lbrakk>\<And> Pred q # \<Gamma>\<rbrakk>\<^sub>\<V>" using assms(1) by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using sequent_validD[OF assms(2) asm_valid] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_PREDL:
  assumes "Pred p \<Zcat> \<Phi> \<in> set \<Gamma>"
    and "\<xi> \<diamondop> Pred p # \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> Pred p # \<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>[OF assms(1)] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using sequent_validD[OF assms(2) asm_valid] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_PREDR:
  assumes "Pred q \<Zcat> \<Psi> \<in> set \<Delta>"
    and "Pred q \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> Pred (\<lambda>s. True) \<Zcat> \<Psi> # remove1 (Pred q \<Zcat> \<Psi>) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (Pred q \<Zcat> \<Psi>) \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence 1: "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> Pred (\<lambda>s. True) \<Zcat> \<Psi> # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(3)])
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>Pred q\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V>" using conj_ins_rem[OF assms(2)] by auto
  also have "... \<subseteq> \<lbrakk>Pred q\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Or> (Pred (\<lambda>s. True) \<Zcat> \<Psi>) # ?\<Delta>\<rbrakk>\<^sub>\<V>" using 1 by auto
  also have "... \<subseteq> \<lbrakk>\<Or> (Pred q \<Zcat> \<Psi>) # ?\<Delta>\<rbrakk>\<^sub>\<V>" by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma REL:
  assumes "Rel R \<in> set \<Gamma>"
    and "Rel R' \<in> set \<Delta>"
    and "\<And>\<V>. \<lbrakk>\<And> Rel R # current_state \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>Rel R'\<rbrakk>\<^sub>\<V>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> Rel R # current_state \<Gamma>\<rbrakk>\<^sub>\<V>" by (rule subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)])
  also have "... \<subseteq> \<lbrakk>Rel R'\<rbrakk>\<^sub>\<V>" by (rule assms(3))
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule subset_\<Psi>[OF assms(2)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma END_ID: 
  assumes "Rel Id \<in> set \<Gamma>"
    and "\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<in> set \<Delta>"
    and "\<xi> \<diamondop> Rel Id # current_state \<Gamma> \<turnstile> [\<Psi>\<^sub>1]"
    and "\<xi> \<diamondop> current_state \<Gamma> \<turnstile> [\<Psi>\<^sub>2]"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?P\<^sub>\<Gamma> = "current_state \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> Rel Id # ?P\<^sub>\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)])
  also have "... \<subseteq> \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> (\<And> ?P\<^sub>\<Gamma>)\<rbrakk>\<^sub>\<V>" 
    using P\<^sub>\<Gamma>_head_only unfolding Id_def by (auto 7 2)
  also have "... \<subseteq> \<lbrakk>\<Psi>\<^sub>1 \<Zcat> (\<And> ?P\<^sub>\<Gamma>)\<rbrakk>\<^sub>\<V>" 
    using sequent_validD[OF assms(3) asm_valid] by (auto 4 6)
  also have "... \<subseteq> \<lbrakk>\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2\<rbrakk>\<^sub>\<V>" using sequent_validD[OF assms(4) asm_valid] by (auto 4 6)
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule subset_\<Psi>[OF assms(2)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_ID:
  assumes "Rel Id \<Zcat> \<Phi> \<in> set \<Gamma>"
    and "\<forall>\<Psi>' \<in> set \<Psi>s. \<exists>\<Psi>. \<Psi> \<Zcat> \<Psi>' \<in> set \<Delta> \<and> \<xi> \<diamondop> Rel Id # current_state \<Gamma> \<turnstile> [\<Psi>]"
    and "\<xi> \<diamondop> \<Phi> # current_state \<Gamma> \<turnstile> \<Psi>s"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?P\<^sub>\<Gamma> = "current_state \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> Rel Id \<Zcat> \<Phi> # ?P\<^sub>\<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)] by auto
  also have "... \<subseteq> \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> \<Phi>\<rbrakk>\<^sub>\<V>" using P\<^sub>\<Gamma>_head_only by (auto 8 2)
  also have "... \<subseteq> \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> (\<And> \<Phi> # ?P\<^sub>\<Gamma>)\<rbrakk>\<^sub>\<V>" 
    unfolding Id_def using P\<^sub>\<Gamma>_head_only by (auto 7 2)
  also have "... \<subseteq> \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>s)\<rbrakk>\<^sub>\<V>" 
    using sequent_validD[OF assms(3) asm_valid] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using assms(2)
  proof (induction \<Psi>s)
    case (Cons \<Psi>' \<Psi>s')
    then obtain \<Psi> where 1: "\<Psi> \<Zcat> \<Psi>' \<in> set \<Delta>" and 2: "\<lbrakk>\<And> Rel Id # ?P\<^sub>\<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>" 
      using asm_valid unfolding sequent_valid_def by auto
    have "\<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>' # \<Psi>s')\<rbrakk>\<^sub>\<V> 
        = \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> \<Psi>'\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>s')\<rbrakk>\<^sub>\<V>" by auto
    also have "... \<subseteq> \<lbrakk>(\<And> Rel Id # ?P\<^sub>\<Gamma>) \<Zcat> \<Psi>'\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using Cons by (auto 7 2)
    also have "... \<subseteq> \<lbrakk>\<Psi> \<Zcat> \<Psi>'\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using 2 by (auto 4 6)
    also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF 1] by auto
    finally show ?case by auto
  qed simp
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

fun spc :: "trace_formula list \<Rightarrow> var \<Rightarrow> aexp \<Rightarrow> (trace_formula)" where
  "spc \<Gamma> x a = Pred (\<lambda>s. \<exists>x'. s\<langle>x\<rangle> = \<bbbA>\<lbrakk>a\<rbrakk>(s\<langle>x \<longmapsto> x'\<rangle>) \<and> 
               (\<forall>\<Phi>\<in>set \<Gamma>. case \<Phi> of Pred p \<Rightarrow> p (s\<langle>x \<longmapsto> x'\<rangle>) \<or> x' = 0 \<and> p (fmdrop x s)))"

lemma Sb_sat_spc:
  assumes "(s, [s']) \<in> \<lbrakk>\<And> Rel (Sb x a) # current_state \<Gamma>\<rbrakk>\<^sub>\<V>"
  shows "(s', \<sigma>) \<in> \<lbrakk>spc (current_state \<Gamma>) x a\<rbrakk>\<^sub>\<V>"
proof -
  have "\<forall>\<Phi>\<in>set (current_state \<Gamma>). 
    case \<Phi> of Pred p \<Rightarrow> p (s'\<langle>x \<longmapsto> s\<langle>x\<rangle>\<rangle>) \<or> s\<langle>x\<rangle> = 0 \<and> p (fmdrop x s')" using assms
  proof (induction \<Gamma>)
    case (Cons \<Phi> \<Gamma>)
    thus ?case
    proof (cases \<Phi>)
      case (Pred p)
      have "p (s'\<langle>x \<longmapsto> s\<langle>x\<rangle>\<rangle>) \<or> s\<langle>x\<rangle> = 0 \<and> p (fmdrop x s')" using Cons
      proof (cases "fmlookup s x")
        case None
        thus ?thesis using Cons Pred 
          by (auto simp add: Sb_def fmdom'_notI fmdrop_fmupd_same fmdrop_idle')
      next
        case (Some b)
        have "s = s'\<langle>x \<longmapsto> s\<langle>x\<rangle>\<rangle>" apply (rule fmap_ext) 
          using Cons Some by (auto simp add: Sb_def)
        thus ?thesis using Pred Cons by auto
      qed
      thus ?thesis using Pred Cons by auto
    qed auto
  qed simp
  moreover have "\<bbbA>\<lbrakk>a\<rbrakk>s = \<bbbA>\<lbrakk>a\<rbrakk>(s\<langle>x \<longmapsto> s\<langle>x\<rangle>\<rangle>)" by (induction a, auto)
  ultimately show ?thesis using assms unfolding Sb_def by auto
qed

lemma END_UPD:
  assumes "Rel (Sb x a) \<in> set \<Gamma>"
    and "\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<in> set \<Delta>"
    and "\<xi> \<diamondop> Rel (Sb x a) # current_state \<Gamma> \<turnstile> [\<Psi>\<^sub>1]"
    and "\<xi> \<diamondop> [spc (current_state \<Gamma>) x a] \<turnstile> [\<Psi>\<^sub>2]"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?P\<^sub>\<Gamma> = "current_state \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)] by auto
  also have "... \<subseteq> \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> spc ?P\<^sub>\<Gamma> x a\<rbrakk>\<^sub>\<V>" using Sb_sat_spc by auto
  also have "... \<subseteq> \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> \<Psi>\<^sub>2\<rbrakk>\<^sub>\<V>" 
    using sequent_validD[OF assms(4) asm_valid] by (auto 4 3)
  also have "... \<subseteq> \<lbrakk>\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2\<rbrakk>\<^sub>\<V>" using sequent_validD[OF assms(3) asm_valid] by (auto 4 6)
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF assms(2)] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_UPD: 
  assumes "Rel (Sb x a)  \<Zcat> \<Phi> \<in> set \<Gamma>"
    and "\<forall>\<Psi>' \<in> set \<Psi>s. \<exists>\<Psi>. \<Psi> \<Zcat> \<Psi>' \<in> set \<Delta> \<and> \<xi> \<diamondop> Rel (Sb x a) # current_state \<Gamma> \<turnstile> [\<Psi>]"
    and "\<xi> \<diamondop> [spc (current_state \<Gamma>) x a, \<Phi>] \<turnstile> \<Psi>s"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?P\<^sub>\<Gamma> = "current_state \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> Rel (Sb x a) \<Zcat> \<Phi> # ?P\<^sub>\<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)] by auto 
  also have "... = \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> \<Phi>\<rbrakk>\<^sub>\<V>" using P\<^sub>\<Gamma>_head_only by (auto 8 2)
  also have "... = \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> (\<And> [spc ?P\<^sub>\<Gamma> x a, \<Phi>])\<rbrakk>\<^sub>\<V>" 
    using Sb_sat_spc by auto
  also have "... \<subseteq> \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>s)\<rbrakk>\<^sub>\<V>" 
    using sequent_validD[OF assms(3) asm_valid] by (auto 6 2)
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using assms(2)
  proof (induction \<Psi>s)
    case (Cons \<Psi>' \<Psi>s')
    then obtain \<Psi> where 2: "\<Psi> \<Zcat> \<Psi>' \<in> set \<Delta>" and 3: "\<lbrakk>\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>" 
      using asm_valid unfolding sequent_valid_def by auto
    have "\<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>' # \<Psi>s')\<rbrakk>\<^sub>\<V>
        = \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> \<Psi>'\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>s')\<rbrakk>\<^sub>\<V>" by auto
    also have "... \<subseteq> \<lbrakk>\<Psi> \<Zcat> \<Psi>'\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>(\<And> Rel (Sb x a) # ?P\<^sub>\<Gamma>) \<Zcat> (\<Or> \<Psi>s')\<rbrakk>\<^sub>\<V>" 
      using 3 by (auto 4 6)
    also have "... \<subseteq> \<lbrakk>\<Psi> \<Zcat> \<Psi>'\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using Cons by auto
    also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF 2] by auto
    finally show ?case by auto
  qed simp
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma ch_assoc: "\<lbrakk>\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3\<rbrakk>\<^sub>\<V> = \<lbrakk>(\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>"
proof
  show "\<lbrakk>\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>(\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>"
    by (simp, rule conjI, blast, rule subsetI, rule UnI2, auto 7 0, metis Cons_eq_appendI append.assoc)
next
  have "{(s\<^sub>0, \<sigma> @ s # \<sigma>') |s\<^sub>0 \<sigma> s \<sigma>'. (s\<^sub>0, \<sigma> @ [s]) \<in> {(s\<^sub>0, \<sigma> @ s # \<sigma>') |s\<^sub>0 \<sigma> s \<sigma>'. (s\<^sub>0, \<sigma> @ [s]) \<in> \<lbrakk>\<Psi>\<^sub>1\<rbrakk>\<^sub>\<V> \<and> \<sigma>' \<noteq> [] \<and> (s, \<sigma>') \<in> \<lbrakk>\<Psi>\<^sub>2\<rbrakk>\<^sub>\<V>} \<and> (s, \<sigma>') \<in> \<lbrakk>\<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>}
    \<subseteq> {(s\<^sub>0, \<sigma> @ s # \<sigma>' @ s' # \<sigma>'') |s\<^sub>0 \<sigma> s \<sigma>' s' \<sigma>''. (s\<^sub>0, \<sigma> @ [s]) \<in> \<lbrakk>\<Psi>\<^sub>1\<rbrakk>\<^sub>\<V> \<and> (s, \<sigma>' @ [s']) \<in> \<lbrakk>\<Psi>\<^sub>2\<rbrakk>\<^sub>\<V> \<and> (s', \<sigma>'') \<in> \<lbrakk>\<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>}"
  proof (auto)
    fix s\<^sub>0 \<sigma> s \<sigma>' \<sigma>'' sa \<sigma>'''
    assume assms: "(s, \<sigma>') \<in> \<lbrakk>\<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>" "\<sigma> @ [s] = \<sigma>'' @ sa # \<sigma>'''" "(s\<^sub>0, \<sigma>'' @ [sa]) \<in> \<lbrakk>\<Psi>\<^sub>1\<rbrakk>\<^sub>\<V>" "\<sigma>''' \<noteq> []" "(sa, \<sigma>''') \<in> \<lbrakk>\<Psi>\<^sub>2\<rbrakk>\<^sub>\<V>"
    then obtain \<sigma>\<sigma> where "\<sigma>''' = \<sigma>\<sigma> @ [s]" by (metis append_butlast_last_id last.simps last_appendR list.discI)
    thus "\<exists>\<sigma>'' sa \<sigma>''' s' \<sigma>''''. \<sigma> @ s # \<sigma>' = \<sigma>'' @ sa # \<sigma>''' @ s' # \<sigma>'''' \<and> (s\<^sub>0, \<sigma>'' @ [sa]) \<in> \<lbrakk>\<Psi>\<^sub>1\<rbrakk>\<^sub>\<V> \<and> (sa, \<sigma>''' @ [s']) \<in> \<lbrakk>\<Psi>\<^sub>2\<rbrakk>\<^sub>\<V> \<and> (s', \<sigma>'''') \<in> \<lbrakk>\<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>" using assms by (auto 5 2)
  qed
  thus "\<lbrakk>(\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3\<rbrakk>\<^sub>\<V>" by (simp, blast 20)
qed

lemma CH_CH_L:
  assumes "(\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3 \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3 # remove1 ((\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 ((\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> (\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" using ch_assoc by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(2) asm_valid])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_CH_R:
  assumes "(\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3 \<in> set \<Delta>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3 # remove1 ((\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 ((\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3) \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3 # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(2)])
  also have "... = \<lbrakk>\<Or> (\<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3 # ?\<Delta>\<rbrakk>\<^sub>\<V>" using ch_assoc by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_DISJ_L:
  assumes "(\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3 \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>3 # remove1 ((\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3) \<Gamma> \<turnstile> \<Delta>"
    and "\<xi> \<diamondop> \<Phi>\<^sub>2 \<Zcat> \<Phi>\<^sub>3 # remove1 ((\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 ((\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> \<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<And> \<Phi>\<^sub>2 \<Zcat> \<Phi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using sequent_validD assms(2,3) asm_valid by blast
qed

lemma CH_DISJ_R: 
  assumes "(\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3 \<in> set \<Delta>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>3 # \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3 # remove1 ((\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 ((\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3) \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Psi>\<^sub>1 \<Zcat> \<Psi>\<^sub>3 # \<Psi>\<^sub>2 \<Zcat> \<Psi>\<^sub>3 # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(2)])
  also have "... \<subseteq> \<lbrakk>\<Or> (\<Psi>\<^sub>1 \<squnion> \<Psi>\<^sub>2) \<Zcat> \<Psi>\<^sub>3 # ?\<Delta>\<rbrakk>\<^sub>\<V>" by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using disj_ins_rem[OF assms(1)] by auto
qed

lemma CH_CONJ_L:
  assumes "(\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3 \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>3 # \<Phi>\<^sub>2 \<Zcat> \<Phi>\<^sub>3 # remove1 ((\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 ((\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> (\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... \<subseteq> \<lbrakk>\<And> \<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>3 # \<Phi>\<^sub>2 \<Zcat> \<Phi>\<^sub>3 # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using sequent_validD[OF assms(2) asm_valid] by auto
qed

lemma ARB1:
  assumes "Pred (\<lambda>s. True) \<Zcat> \<Psi> \<in> set \<Delta>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi> # remove1 (Pred (\<lambda>s. True) \<Zcat> \<Psi>) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (Pred (\<lambda>s. True) \<Zcat> \<Psi>) \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Psi> # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(2)])
  also have "... \<subseteq> \<lbrakk>\<Or> Pred (\<lambda>s. True) \<Zcat> \<Psi> # ?\<Delta>\<rbrakk>\<^sub>\<V>" by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma ARB2:
  assumes "Pred (\<lambda>s. True) \<Zcat> \<Psi> \<in> set \<Delta>"
    and "\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>2 \<in> set \<Gamma>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Phi>\<^sub>1 \<Zcat> Pred (\<lambda>s. True) \<Zcat> \<Psi> # remove1 (Pred (\<lambda>s. True) \<Zcat> \<Psi>) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (Pred (\<lambda>s. True) \<Zcat> \<Psi>) \<Delta>"
  fix \<V>
  assume "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> (\<Phi>\<^sub>1 \<Zcat> Pred (\<lambda>s. True) \<Zcat> \<Psi>) # ?\<Delta>\<rbrakk>\<^sub>\<V>" 
    by (rule sequent_validD[OF assms(3)])
  also have "... = \<lbrakk>\<Phi>\<^sub>1 \<Zcat> Pred (\<lambda>s. True) \<Zcat> \<Psi>\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<Or> ?\<Delta>\<rbrakk>\<^sub>\<V>" by auto
  also have "... = \<lbrakk>(\<Phi>\<^sub>1 \<Zcat> Pred (\<lambda>s. True)) \<Zcat> \<Psi>\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<Or> ?\<Delta>\<rbrakk>\<^sub>\<V>" using ch_assoc by blast
  also have "... \<subseteq> \<lbrakk>\<Or> Pred (\<lambda>s. True) \<Zcat> \<Psi> # ?\<Delta>\<rbrakk>\<^sub>\<V>" by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma \<mu>_lfp: "\<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V> = lfp (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>)" by (simp add: lfp_def)

lemma sem_monotone: "\<And>\<V>. mono (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>)"
proof (rule monoI, induction \<Phi>)
  case (Fixed_Point X' \<Phi>)
  show ?case using Fixed_Point(1)[OF Fixed_Point(2)]
    by (cases "X' = X", auto 6 2 simp add: fmupd_reorder_neq)
qed (auto 13 2)

lemma var_not_free_val_independent:
  assumes "X \<notin> free_vars \<Phi>"
  shows "\<And>\<V> \<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>"
  using assms
proof (induction \<Phi>)
  case (Fixed_Point X' \<Phi>)
  thus ?case by (cases "X = X'", auto simp add: fmupd_reorder_neq)
qed auto

lemma subst_var_syntax_sem:
  assumes "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>'"
  shows "\<And>\<V>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<lbrakk>\<Phi>'\<rbrakk>\<^sub>\<V>\<rangle> = \<lbrakk>(\<Phi> \<lbrakk>\<Phi>' / X\<rbrakk>)\<rbrakk>\<^sub>\<V>"
  using assms
proof (induction \<Phi>)
  case (Fixed_Point X' \<Phi>)
  hence 1: "X' \<notin> free_vars \<Phi>'" by auto
  show ?case
  proof (cases "X = X'")
    case False
    have "\<lbrakk>\<mu> X'. \<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<lbrakk>\<Phi>'\<rbrakk>\<^sub>\<V>\<rangle> = \<Inter> {\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<lbrakk>\<Phi>'\<rbrakk>\<^sub>\<V>\<rangle>\<langle>X' \<longmapsto> \<gamma>\<rangle> \<subseteq> \<gamma>}" by auto
    also have "... = \<Inter> {\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X' \<longmapsto> \<gamma>\<rangle>\<langle>X \<longmapsto> \<lbrakk>\<Phi>'\<rbrakk>\<^sub>\<V>\<rangle> \<subseteq> \<gamma>}"
      by (simp add: fmupd_reorder_neq[OF False])
    also have "... = \<Inter> {\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X' \<longmapsto> \<gamma>\<rangle>\<langle>X \<longmapsto> \<lbrakk>\<Phi>'\<rbrakk>\<^sub>\<V>\<langle>X' \<longmapsto> \<gamma>\<rangle>\<rangle> \<subseteq> \<gamma>}"
      using var_not_free_val_independent[OF 1] by auto
    also have "... = \<Inter> {\<gamma>. \<lbrakk>\<Phi> \<lbrakk>\<Phi>' / X\<rbrakk>\<rbrakk>\<^sub>\<V>\<langle>X' \<longmapsto> \<gamma>\<rangle> \<subseteq> \<gamma>}"
      using Fixed_Point by auto
    also have "... = \<lbrakk>\<mu> X'. (\<Phi> \<lbrakk>\<Phi>' / X\<rbrakk>)\<rbrakk>\<^sub>\<V>" by auto
    also have "... = \<lbrakk>(\<mu> X'. \<Phi>) \<lbrakk>\<Phi>' / X\<rbrakk>\<rbrakk>\<^sub>\<V>" using False by auto
    finally show ?thesis by auto
  qed simp
qed auto

lemma \<mu>_unf:
  assumes "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>"
  shows "\<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<Phi>\<lbrakk>\<mu> X. \<Phi> / X\<rbrakk>\<rbrakk>\<^sub>\<V>"
proof -
  have 1: "\<forall>X' \<in> bound_vars \<Phi>. X' \<notin> free_vars (\<mu> X. \<Phi>)" using assms by auto
  have "\<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V>\<rangle>"
    using lfp_unfold[OF sem_monotone] \<mu>_lfp by auto
  also have "... = \<lbrakk>\<Phi> \<lbrakk>\<mu> X. \<Phi> / X\<rbrakk>\<rbrakk>\<^sub>\<V>" by (rule subst_var_syntax_sem[OF 1])
  finally show ?thesis by auto
qed

lemma UNFL:
  assumes "\<mu> X. \<Phi> \<in> set \<Gamma>"
    and "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>"
    and "\<xi> \<diamondop> \<Phi>\<lbrakk>\<mu> X. \<Phi> / X\<rbrakk> # remove1 (\<mu> X. \<Phi>) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 (\<mu> X. \<Phi>) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> \<mu> X. \<Phi> # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> \<Phi>\<lbrakk>\<mu> X. \<Phi> / X\<rbrakk> # ?\<Gamma>\<rbrakk>\<^sub>\<V>" using \<mu>_unf[OF assms(2)] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(3) asm_valid])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma UNFR:
  assumes "\<mu> X. \<Psi> \<in> set \<Delta>"
    and "\<forall>X \<in> bound_vars \<Psi>. X \<notin> free_vars \<Psi>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Psi>\<lbrakk>\<mu> X. \<Psi> / X\<rbrakk> # remove1 (\<mu> X. \<Psi>) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (\<mu> X. \<Psi>) \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Psi>\<lbrakk>\<mu> X. \<Psi> / X\<rbrakk> # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(3)])
  also have "... = \<lbrakk>\<Or> \<mu> X. \<Psi> # ?\<Delta>\<rbrakk>\<^sub>\<V>" using \<mu>_unf[OF assms(2)] by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_UNFL:
  assumes "(\<mu> X. \<Phi>) \<Zcat> \<Phi>' \<in> set \<Gamma>"
    and "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>"
    and "\<xi> \<diamondop> (\<Phi>\<lbrakk>\<mu> X. \<Phi> / X\<rbrakk>) \<Zcat> \<Phi>' # remove1 ((\<mu> X. \<Phi>) \<Zcat> \<Phi>') \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 ((\<mu> X. \<Phi>) \<Zcat> \<Phi>') \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> (\<mu> X. \<Phi>) \<Zcat> \<Phi>' # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> (\<Phi>\<lbrakk>\<mu> X. \<Phi> / X\<rbrakk>) \<Zcat> \<Phi>' # ?\<Gamma>\<rbrakk>\<^sub>\<V>" using \<mu>_unf[OF assms(2)] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(3) asm_valid])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_UNFR:
  assumes "(\<mu> X. \<Psi>) \<Zcat> \<Psi>' \<in> set \<Delta>"
    and "\<forall>X \<in> bound_vars \<Psi>. X \<notin> free_vars \<Psi>"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> (\<Psi>\<lbrakk>\<mu> X. \<Psi> / X\<rbrakk>) \<Zcat> \<Psi>' # remove1 ((\<mu> X. \<Psi>) \<Zcat> \<Psi>') \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 ((\<mu> X. \<Psi>) \<Zcat> \<Psi>') \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> (\<Psi>\<lbrakk>\<mu> X. \<Psi> / X\<rbrakk>) \<Zcat> \<Psi>' # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(3)])
  also have "... = \<lbrakk>\<Or> (\<mu> X. \<Psi>) \<Zcat> \<Psi>' # ?\<Delta>\<rbrakk>\<^sub>\<V>" using \<mu>_unf[OF assms(2)] by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

primrec repeat :: "nat \<Rightarrow> string \<Rightarrow> trace_formula \<Rightarrow> trace_formula" where
  "repeat 0 X \<Phi> = \<Phi>" |
  "repeat (Suc i) X \<Phi> = \<Phi> \<lbrakk>repeat i X \<Phi> / X\<rbrakk>"

lemma free_var_replace_upper_bound: "free_vars (\<Phi>\<lbrakk>\<Phi>' / X\<rbrakk>) \<subseteq> free_vars \<Phi> \<union> free_vars \<Phi>'"
  by (induction \<Phi>, auto)

lemma free_var_repeat: 
  assumes "\<forall>X\<^sub>1 \<in> (bound_vars \<Phi>). X\<^sub>1 \<notin> free_vars \<Phi>"
  shows "\<forall>X\<^sub>1 \<in> bound_vars \<Phi>. X\<^sub>1 \<notin> free_vars (repeat i X \<Phi>)"
  using free_var_replace_upper_bound assms by (induction i, auto 6 2)

lemma \<mu>_len:
  assumes "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>"
  shows "\<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<mu> X. repeat i X \<Phi>\<rbrakk>\<^sub>\<V>"
proof -
  have 1: "(\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>) ^^ Suc i = (\<lambda>\<gamma>. \<lbrakk>repeat i X \<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>)"
  proof (induction i)
    case (Suc i)
    have "(\<lambda>\<gamma>. \<lbrakk>repeat (Suc i) X \<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>) = (\<lambda>\<gamma>. \<lbrakk>\<Phi> \<lbrakk>repeat i X \<Phi> / X\<rbrakk>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>)" 
      by simp
    also have "... = (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>\<langle>X \<longmapsto> \<lbrakk>repeat i X \<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>\<rangle>)" 
      using subst_var_syntax_sem[OF free_var_repeat[OF assms]] by blast
    also have "... = (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<lbrakk>repeat i X \<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>\<rangle>)" by auto
    also have "... = (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> ((\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>) ^^ (Suc i)) \<gamma>\<rangle>)" 
      using Suc by presburger
    also have "... = (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>) ^^ (i + 2)" by auto
    finally show ?case by auto
  qed simp
  have "\<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V> = lfp ((\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>) ^^ Suc i)" 
    using lfp_funpow[OF sem_monotone] \<mu>_lfp by auto
  also have "... = lfp (\<lambda>\<gamma>. \<lbrakk>repeat i X \<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>)" using 1 by auto
  also have "... = \<lbrakk>\<mu> X. repeat i X \<Phi>\<rbrakk>\<^sub>\<V>" using \<mu>_lfp by auto
  finally show ?thesis by auto
qed

lemma LENL:
  assumes "\<mu> X. \<Phi> \<in> set \<Gamma>"
    and "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>"
    and "i \<ge> 1"
    and "\<xi> \<diamondop> \<mu> X. (repeat i X \<Phi>) # remove1 (\<mu> X. \<Phi>) \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 (\<mu> X. \<Phi>) \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> \<mu> X. \<Phi> # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> \<mu> X. (repeat i X \<Phi>) # ?\<Gamma>\<rbrakk>\<^sub>\<V>" using \<mu>_len[OF assms(2)] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(4) asm_valid])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma LENR:
  assumes "\<mu> X. \<Psi> \<in> set \<Delta>"
    and "\<forall>X \<in> bound_vars \<Psi>. X \<notin> free_vars \<Psi>"
    and "i \<ge> 1"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> \<mu> X. (repeat i X \<Psi>) # remove1 (\<mu> X. \<Psi>) \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 (\<mu> X. \<Psi>) \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<mu> X. (repeat i X \<Psi>) # ?\<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(4)])
  also have "... = \<lbrakk>\<Or> (\<mu> X. \<Psi>) # ?\<Delta>\<rbrakk>\<^sub>\<V>" using \<mu>_len[OF assms(2)] by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_LENL:
  assumes "(\<mu> X. \<Phi>) \<Zcat> \<Phi>' \<in> set \<Gamma>"
    and "\<forall>X \<in> bound_vars \<Phi>. X \<notin> free_vars \<Phi>"
    and "i \<ge> 1"
    and "\<xi> \<diamondop> (\<mu> X. (repeat i X \<Phi>)) \<Zcat> \<Phi>' # remove1 ((\<mu> X. \<Phi>) \<Zcat> \<Phi>') \<Gamma> \<turnstile> \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Gamma> = "remove1 ((\<mu> X. \<Phi>) \<Zcat> \<Phi>') \<Gamma>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> = \<lbrakk>\<And> (\<mu> X. \<Phi>) \<Zcat> \<Phi>' # ?\<Gamma>\<rbrakk>\<^sub>\<V>" by (rule conj_ins_rem[OF assms(1)])
  also have "... = \<lbrakk>\<And> (\<mu> X. (repeat i X \<Phi>)) \<Zcat> \<Phi>' # ?\<Gamma>\<rbrakk>\<^sub>\<V>" using \<mu>_len[OF assms(2)] by auto
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule sequent_validD[OF assms(4) asm_valid])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma CH_LENR: 
  assumes "(\<mu> X. \<Psi>) \<Zcat> \<Psi>' \<in> set \<Delta>"
    and "\<forall>X \<in> bound_vars \<Psi>. X \<notin> free_vars \<Psi>"
    and "i \<ge> 1"
    and "\<xi> \<diamondop> \<Gamma> \<turnstile> (\<mu> X. (repeat i X \<Psi>)) \<Zcat> \<Psi>' # remove1 ((\<mu> X. \<Psi>) \<Zcat> \<Psi>') \<Delta>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  let ?\<Delta> = "remove1 ((\<mu> X. \<Psi>) \<Zcat> \<Psi>') \<Delta>"
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  hence "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> (\<mu> X. repeat i X \<Psi>) \<Zcat> \<Psi>' # ?\<Delta>\<rbrakk>\<^sub>\<V>" 
    by (rule sequent_validD[OF assms(4)])
  also have "... = \<lbrakk>\<Or> (\<mu> X. \<Psi>) \<Zcat> \<Psi>' # ?\<Delta>\<rbrakk>\<^sub>\<V>" using \<mu>_len[OF assms(2)] by auto
  also have "... = \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by (rule disj_ins_rem[OF assms(1)])
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma RVAR:
  assumes "RVar X \<in> set \<Gamma>"
    and "(X, p, \<Psi>) \<in> \<xi>"
    and "\<Psi> \<in> set \<Delta>"
    and "\<And>\<V>. \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>Pred p\<rbrakk>\<^sub>\<V>"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>RVar X\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)] by auto
  also have "... \<subseteq> \<lbrakk>RVar X \<sqinter> Pred p\<rbrakk>\<^sub>\<V>" using assms(4) by auto
  also have "... \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>" using assms(2) asm_valid by (auto 8 2)
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF assms(3)] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma FPI:
  assumes "\<mu> X\<^sub>1. \<Phi> \<in> set \<Gamma>"
    and "\<mu> X\<^sub>2. \<Psi> \<in> set \<Delta>"
    and "X\<^sub>1 \<notin> free_vars \<Psi>"
    and "X\<^sub>2 \<notin> free_vars \<Phi>"
    and "\<And>\<V> \<gamma>\<^sub>1 \<gamma>\<^sub>2. assumption_valid \<xi> \<V> \<Longrightarrow> assumption_valid \<xi> (\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<^sub>1\<rangle>\<langle>X\<^sub>2 \<longmapsto> \<gamma>\<^sub>2\<rangle>)"
    and "\<And>\<V>. \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V>"
    and "insert (X\<^sub>1, I, RVar X\<^sub>2) \<xi> \<diamondop> [Pred I, \<Phi>] \<turnstile> [\<Psi>]"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> \<mu> X\<^sub>1. \<Phi> # current_state \<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)] by auto
  also have "... \<subseteq> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<mu> X\<^sub>1. \<Phi>\<rbrakk>\<^sub>\<V>" using assms(6) by auto
  also have "... = \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> lfp (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>)" using \<mu>_lfp by auto
  also have "... \<subseteq> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>"
  proof (rule lfp_ordinal_induct_set[OF sem_monotone])
    show "\<And>M. \<forall>S\<in>M. \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> S \<subseteq> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V> \<Longrightarrow> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<Union> M \<subseteq> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>" by auto
  next
    fix \<gamma>
    assume "\<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<gamma> \<subseteq> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>"
    hence "\<lbrakk>\<And> [RVar X\<^sub>1, Pred I]\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle> 
        \<subseteq> \<lbrakk>RVar X\<^sub>2\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle>" by auto
    hence "\<lbrakk>\<And> [Pred I, \<Phi>]\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle> 
        \<subseteq> \<lbrakk>\<Or> [\<Psi>]\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle>" 
      using sequent_validD[OF assms(7)] assms(5)[OF asm_valid] by simp
    hence 1: "\<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle>" 
      using var_not_free_val_independent[OF assms(4)] by auto
    hence "\<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle>"
    proof (cases "X\<^sub>1 = X\<^sub>2")
      case False
      hence "\<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>2 \<longmapsto> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>\<rangle>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle>" 
        using 1 fmupd_reorder_neq[of X\<^sub>1 X\<^sub>2 \<gamma>] by auto
      thus ?thesis using var_not_free_val_independent[OF assms(3)] by auto
    qed simp
    thus "\<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X\<^sub>1 \<longmapsto> \<gamma>\<rangle> \<subseteq> \<lbrakk>\<mu> X\<^sub>2. \<Psi>\<rbrakk>\<^sub>\<V>" 
      using lfp_unfold[OF sem_monotone] \<mu>_lfp by auto
  qed
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF assms(2)] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

lemma FPI_ALT: 
  assumes "\<mu> X. \<Phi> \<in> set \<Gamma>"
    and "\<Psi> \<in> set \<Delta>"
    and "X \<notin> free_vars \<Psi>"
    and "\<And>\<V> \<gamma>. assumption_valid \<xi> \<V> \<Longrightarrow> assumption_valid \<xi> (\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>)"
    and "\<And>\<V>. \<lbrakk>\<And> current_state \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V>"
    and "insert (X, I, \<Psi>) \<xi> \<diamondop> [Pred I, \<Phi>] \<turnstile> [\<Psi>]"
  shows "\<xi> \<diamondop> \<Gamma> \<turnstile> \<Delta>"
proof (rule sequent_validI)
  fix \<V>
  assume asm_valid: "assumption_valid \<xi> \<V>"
  have "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<And> \<mu> X. \<Phi> # current_state \<Gamma>\<rbrakk>\<^sub>\<V>" using subset_\<Phi>_P\<^sub>\<Gamma>[OF assms(1)] by auto
  also have "... \<subseteq> lfp (\<lambda>\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle>) \<inter> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V>" using assms(5) \<mu>_lfp by auto
  also have "... \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>"
    proof (rule lfp_ordinal_induct_set[OF sem_monotone])
      show "\<And>M. \<forall>S\<in>M. S \<inter> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V> \<Longrightarrow> \<Union> M \<inter> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>" by auto
      fix S
      assume "S \<inter> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>"
      hence "\<lbrakk>RVar X\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> S\<rangle> \<inter> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> S\<rangle> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> S\<rangle>" 
        using var_not_free_val_independent[OF assms(3)] by auto
      hence "\<lbrakk>\<And> [Pred I, \<Phi>]\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> S\<rangle> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> S\<rangle>" 
        using assms(4)[OF asm_valid] sequent_validD[OF assms(6)] by simp
      thus "\<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> S\<rangle> \<inter> \<lbrakk>Pred I\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Psi>\<rbrakk>\<^sub>\<V>" 
        using var_not_free_val_independent[OF assms(3)] by auto
    qed
  also have "... \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" using subset_\<Psi>[OF assms(2)] by auto
  finally show "\<lbrakk>\<And> \<Gamma>\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>\<Or> \<Delta>\<rbrakk>\<^sub>\<V>" by auto
qed

end