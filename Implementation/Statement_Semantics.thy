theory Statement_Semantics
  imports Basics
begin

abbreviation restrict :: "trace set \<Rightarrow> bexp \<Rightarrow> trace set" ("_|\<^sub>r_" [70, 75] 75) where
  "A|\<^sub>rb \<equiv> {(s, \<sigma>) | s \<sigma>.(s, \<sigma>) \<in> A \<and> s \<Turnstile> b}"

abbreviation repeat_first_state :: "trace set \<Rightarrow> trace set" ("\<sharp>_" [70] 70) where
  "\<sharp>A \<equiv> {(s, [s] @ \<sigma>) | s \<sigma>.(s, \<sigma>) \<in> A}"

abbreviation chop :: "trace set \<Rightarrow> trace set \<Rightarrow> trace set" ("_\<Zcat>\<^sub>t_" [70, 71] 70) where
  "A \<Zcat>\<^sub>t B \<equiv> {(s, \<sigma>) | s \<sigma>.(s, []) \<in> A \<and> (s, \<sigma>) \<in> B} \<union>
    {(s, \<sigma> @ s' # \<sigma>') | s \<sigma> s' \<sigma>'.(s, \<sigma> @ [s']) \<in> A \<and> (s', \<sigma>') \<in> B}"

primrec statement_semantics :: "S \<Rightarrow> (stm_var \<Rightarrow> trace set) \<Rightarrow> (method_name \<Rightarrow> trace set) \<Rightarrow> trace set"
  ("\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>_\<rbrakk>\<^sub>_\<^sub>,\<^sub>_" [55, 80, 80] 80) where
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>SKIP\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = {(s, [s]) | s. True}" |
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>x := a\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = {(s, [s']) | s s'. s' = s\<langle>x \<longmapsto> \<bbbA>\<lbrakk>a\<rbrakk>(s)\<rangle>}" |
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<^sub>1;;S\<^sub>2\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<^sub>1\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> \<Zcat>\<^sub>t \<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<^sub>2\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>" |
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>IF b THEN S\<^sub>1 ELSE S\<^sub>2 FI\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = (\<sharp>\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<^sub>1\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>)|\<^sub>rb \<union> (\<sharp>\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>S\<^sub>2\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I>)|\<^sub>r(Not b)" |
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>Call m\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<rho>(m)" |
  "\<S>\<^sub>\<t>\<^sub>\<r>\<lbrakk>SVar sv\<rbrakk>\<^sub>\<rho>\<^sub>,\<^sub>\<I> = \<I>(sv)"

primrec subst_method_call :: "S \<Rightarrow> S \<Rightarrow> string \<Rightarrow> S"
  ("_ \<lbrakk>_ '/ _\<rbrakk>" [75, 65, 65] 74) where
  "SKIP \<lbrakk>S' / m\<rbrakk> = SKIP" |
  "(x := a) \<lbrakk>S' / m\<rbrakk> = x := a" |
  "(S\<^sub>1;;S\<^sub>2) \<lbrakk>S' / m\<rbrakk> = S\<^sub>1 \<lbrakk>S' / m\<rbrakk>;;S\<^sub>2 \<lbrakk>S' / m\<rbrakk>" |
  "(IF b THEN S\<^sub>1 ELSE S\<^sub>2 FI) \<lbrakk>S' / m\<rbrakk> = IF b THEN S\<^sub>1 \<lbrakk>S' / m\<rbrakk> ELSE S\<^sub>2 \<lbrakk>S' / m\<rbrakk> FI" |
  "(Call m') \<lbrakk>S' / m\<rbrakk> = (if m' = m then S' else Call m')" |
  "(SVar sv) \<lbrakk>S' / m\<rbrakk> = (SVar sv)"

end