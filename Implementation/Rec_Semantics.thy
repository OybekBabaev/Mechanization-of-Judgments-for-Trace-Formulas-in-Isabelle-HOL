theory Rec_Semantics
  imports "Statement_Semantics" "Trace_Formulas"
begin

definition sem_ops :: "(method_name, S) fmap \<Rightarrow>
  (stm_var \<Rightarrow> trace set) \<Rightarrow> (method_name \<Rightarrow> trace set) \<Rightarrow> (method_name \<Rightarrow> trace set)" where
  "sem_ops T \<I> \<rho> = (\<lambda>m. case fmlookup T m of None \<Rightarrow> {} | Some S\<^sub>m \<Rightarrow> \<sharp>\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<^sub>m\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>)"

definition initial_interpretation :: "(method_name, S) fmap \<Rightarrow>
  (stm_var \<Rightarrow> trace set) \<Rightarrow> (method_name \<Rightarrow> trace set)" 
  ("\<rho>\<^sub>0(_)(_)" [70, 70] 70) where
  "\<rho>\<^sub>0(T)(\<I>) = lfp (sem_ops T \<I>)"

definition rec_sem :: "Rec \<Rightarrow> (stm_var \<Rightarrow> trace set) \<Rightarrow> trace set" ("\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>_\<rbrakk>\<^sub>_") where
  "rec_sem R \<I> = (case R of (S, T) \<Rightarrow> (let \<rho> = \<rho>\<^sub>0 T \<I> in \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>))"

lemma statement_semantics_mono: "(\<forall>m. \<rho> m \<subseteq> \<rho>' m) \<Longrightarrow> \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> \<subseteq> \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<rbrakk>\<^sub>\<rho>'\<^sub>,\<^sub>\<I>"
  apply (induction S)
  apply simp_all
  by blast+

lemma sem_ops_mono: "mono (sem_ops T \<I>)"
  apply (rule monoI)
  apply (simp add: sem_ops_def le_fun_def)
  apply clarsimp
  apply (split option.splits)
  apply (rule conjI)
  apply (fastforce split: option.splits)
  apply (clarsimp split: option.splits)
  apply (rule subsetD[OF statement_semantics_mono])
  by assumption+

lemma \<rho>\<^sub>0_fixpoint: "sem_ops T \<I> (\<rho>\<^sub>0 T \<I>) = \<rho>\<^sub>0 T \<I>"
  unfolding initial_interpretation_def
  by (rule lfp_unfold[OF sem_ops_mono, symmetric])

end