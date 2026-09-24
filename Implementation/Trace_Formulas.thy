theory Trace_Formulas
  imports Basics
begin

datatype trace_formula = Pred "state \<Rightarrow> bool" |
  Rel "(state \<times> state) set" |
  Conj trace_formula trace_formula (infix "\<sqinter>" 61) |
  Disj trace_formula trace_formula (infixr "\<squnion>" 60) |
  Chop trace_formula trace_formula (infixr "\<Zcat>" 70) |
  RVar string |
  Fixed_Point string trace_formula ("\<mu> _. _" [60, 75] 75)

primrec semantics :: "trace_formula \<Rightarrow> (string, trace set) fmap \<Rightarrow> trace set" 
  ("\<lbrakk>_\<rbrakk>\<^sub>_" [60, 71] 71) where
  "\<lbrakk>Pred p\<rbrakk>\<^sub>\<V> = {(s, \<sigma>) | s \<sigma>. p s}" |
  "\<lbrakk>Rel R\<rbrakk>\<^sub>\<V> = {(s, [s']) | s s'. (s, s') \<in> R}" |
  "\<lbrakk>\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2\<rbrakk>\<^sub>\<V> = \<lbrakk>\<Phi>\<^sub>1\<rbrakk>\<^sub>\<V> \<inter> \<lbrakk>\<Phi>\<^sub>2\<rbrakk>\<^sub>\<V>" |
  "\<lbrakk>\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2\<rbrakk>\<^sub>\<V> = \<lbrakk>\<Phi>\<^sub>1\<rbrakk>\<^sub>\<V> \<union> \<lbrakk>\<Phi>\<^sub>2\<rbrakk>\<^sub>\<V>" |
  "\<lbrakk>\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>2\<rbrakk>\<^sub>\<V> = {(s, \<sigma>) | s \<sigma>. (s, []) \<in> \<lbrakk>\<Phi>\<^sub>1\<rbrakk>\<^sub>\<V> \<and> (s, \<sigma>) \<in> \<lbrakk>\<Phi>\<^sub>2\<rbrakk>\<^sub>\<V>} \<union>
                {(s\<^sub>0, \<sigma> @ s # \<sigma>') | s\<^sub>0 \<sigma> s \<sigma>'. (s\<^sub>0, \<sigma> @ [s]) \<in> \<lbrakk>\<Phi>\<^sub>1\<rbrakk>\<^sub>\<V> \<and> (s, \<sigma>') \<in> \<lbrakk>\<Phi>\<^sub>2\<rbrakk>\<^sub>\<V>}" |
  "\<lbrakk>RVar X\<rbrakk>\<^sub>\<V> = (case fmlookup \<V> X of Some \<gamma> \<Rightarrow> \<gamma>)" |
  "\<lbrakk>\<mu> X. \<Phi>\<rbrakk>\<^sub>\<V> = \<Inter> {\<gamma>. \<lbrakk>\<Phi>\<rbrakk>\<^sub>\<V>\<langle>X \<longmapsto> \<gamma>\<rangle> \<subseteq> \<gamma>}"

definition Id :: "(state \<times> state) set" where
  "Id \<equiv> {(s, s'). s' = s}"

definition Sb :: "var \<Rightarrow> aexp \<Rightarrow> (state \<times> state) set" where
  "Sb x a \<equiv> {(s, s'). s' = s\<langle>x \<longmapsto> \<bbbA>\<lbrakk>a\<rbrakk>(s)\<rangle>}"

function stf :: "Rec \<Rightarrow> trace_formula" where
  "stf (SKIP, T) = Rel Id" |
  "stf (Assign x a, T) = Rel (Sb x a)" |
  "stf (s1;; s2, T) = stf (s1, T) \<Zcat> stf (s2, T)" |
  "stf (IF b THEN s1 ELSE s2 FI, T) = Pred (\<lambda>s. s \<Turnstile> b) \<sqinter> Rel Id \<Zcat> stf (s1, T) \<squnion> 
         Pred (\<lambda>s. \<not> s \<Turnstile> b) \<sqinter> Rel Id \<Zcat> stf (s2, T)" |
  "stf (Call m, T) = Rel Id \<Zcat> (if m |\<in>| fmdom T
         then \<mu> m. stf (the (fmlookup T m), fmdrop m T)
         else RVar m)" |
  "stf (SVar sv, T) = Pred (\<lambda>s. False)"
  by pat_completeness auto
termination
  by (relation "measures [(\<lambda>(_, T). size (fmdom T)), (\<lambda>(\<Phi>, _). size \<Phi>)]")
     (auto 4 3 simp add: card_gt_0_iff intro: diff_Suc_less)

primrec subst_rvar :: "trace_formula \<Rightarrow> trace_formula \<Rightarrow> string \<Rightarrow> trace_formula" 
    ("_ \<lbrakk>_ '/ _\<rbrakk>" [75, 65, 65] 74) where
  "Pred p\<lbrakk>\<Phi> / X\<rbrakk> = Pred p" |
  "Rel R\<lbrakk>\<Phi> / X\<rbrakk> = Rel R" |
  "(\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2)\<lbrakk>\<Phi> / X\<rbrakk> = \<Phi>\<^sub>1 \<lbrakk>\<Phi> / X\<rbrakk> \<sqinter> \<Phi>\<^sub>2 \<lbrakk>\<Phi> / X\<rbrakk>" |
  "(\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) \<lbrakk>\<Phi> / X\<rbrakk> = \<Phi>\<^sub>1 \<lbrakk>\<Phi> / X\<rbrakk> \<squnion> \<Phi>\<^sub>2 \<lbrakk>\<Phi> / X\<rbrakk>" |
  "(\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>2) \<lbrakk>\<Phi> / X\<rbrakk> = \<Phi>\<^sub>1 \<lbrakk>\<Phi> / X\<rbrakk> \<Zcat> \<Phi>\<^sub>2 \<lbrakk>\<Phi> / X\<rbrakk>" |
  "RVar X'\<lbrakk>\<Phi> / X\<rbrakk> = (if X = X' then \<Phi> else RVar X')" |
  "(\<mu> X'. \<Phi>\<^sub>1)\<lbrakk>\<Phi> / X\<rbrakk> = (if X = X' then \<mu> X'. \<Phi>\<^sub>1 else \<mu> X'. (\<Phi>\<^sub>1 \<lbrakk>\<Phi> / X\<rbrakk>))"

primrec bound_vars :: "trace_formula \<Rightarrow> string set" where
  "bound_vars (Pred _) = {}" |
  "bound_vars (Rel _) = {}" |
  "bound_vars (\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) = bound_vars \<Phi>\<^sub>1 \<union> bound_vars \<Phi>\<^sub>2" |
  "bound_vars (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) = bound_vars \<Phi>\<^sub>1 \<union> bound_vars \<Phi>\<^sub>2" |
  "bound_vars (\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>2) = bound_vars \<Phi>\<^sub>1 \<union> bound_vars \<Phi>\<^sub>2" |
  "bound_vars (RVar _) = {}" |
  "bound_vars (\<mu> X. \<Phi>) = insert X (bound_vars \<Phi>)"

primrec free_vars :: "trace_formula \<Rightarrow> string set" where 
  "free_vars (Pred _) = {}" | 
  "free_vars (Rel _) = {}" | 
  "free_vars (\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) = free_vars \<Phi>\<^sub>1 \<union> free_vars \<Phi>\<^sub>2" | 
  "free_vars (\<Phi>\<^sub>1 \<squnion> \<Phi>\<^sub>2) = free_vars \<Phi>\<^sub>1 \<union> free_vars \<Phi>\<^sub>2" | 
  "free_vars (\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>2) = free_vars \<Phi>\<^sub>1 \<union> free_vars \<Phi>\<^sub>2" |
  "free_vars (RVar X) = {X}" |
  "free_vars (\<mu> X. \<Phi>) = (free_vars \<Phi>) - {X}"

end