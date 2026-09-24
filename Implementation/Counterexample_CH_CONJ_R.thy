theory Counterexample_CH_CONJ_R
  imports Trace_Formulas
begin

definition s\<^sub>1 :: "state" where
  "s\<^sub>1 \<equiv> fmap_of_list [(''x'', 1)]"

definition s\<^sub>2 :: "state" where
  "s\<^sub>2 \<equiv> fmap_of_list [(''x'', 2)]"

definition \<V> :: "(string, trace set) fmap" where
  "\<V> \<equiv> fmap_of_list [(''1'', {(s\<^sub>1, [])}),
                      (''2'', {(s\<^sub>1, [s\<^sub>2])}),
                      (''3'', {(s\<^sub>1, [s\<^sub>2]), (s\<^sub>2, [])}),
                      (''4'', {(s\<^sub>1, [s\<^sub>2])})]"

lemma "\<lbrakk>RVar ''4''\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>RVar ''1'' \<Zcat> RVar ''3''\<rbrakk>\<^sub>\<V>"
  by (simp add: \<V>_def)

lemma "\<lbrakk>RVar ''4''\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>RVar ''2'' \<Zcat> RVar ''3''\<rbrakk>\<^sub>\<V>"
  by (simp add: \<V>_def)

lemma "\<not>(\<lbrakk>RVar ''4''\<rbrakk>\<^sub>\<V> \<subseteq> \<lbrakk>(RVar ''1'' \<sqinter> RVar ''2'') \<Zcat> RVar ''3''\<rbrakk>\<^sub>\<V>)"
  by (simp add: \<V>_def)

end