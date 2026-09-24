theory Example_Pow
  imports "../TFI_Prover"
begin

notation fmap_of_list ("fm")

(* MA example 8.3 *)
definition S_pow :: Rec where 
"S_pow \<equiv> (''z'' := Num 1;; Call ''pow'',
fm [(''pow'', IF (Var ''x'' == Num 1) 
              THEN SKIP;; ''f'' := Num 1 
              ELSE ''z'' := Var ''z'' \<otimes> Var ''y'';; Call ''subtract'' FI),
(''subtract'', ''x'' := Var ''x'' \<ominus> Num 1;; Call ''pow'')])"

definition R_stat :: "var \<Rightarrow> (state \<times> state) set" where
  "R_stat x \<equiv> {(s, s'). s\<langle>x\<rangle> = s'\<langle>x\<rangle>}"

definition R_change :: "var \<Rightarrow> (state \<times> state) set" where
  "R_change x \<equiv> {(s, s'). s\<langle>x\<rangle> \<noteq> s'\<langle>x\<rangle>}"

declare R_stat_def [rels]
declare R_change_def [rels]

(* MA example 8.3 A *)
lemma "[stf S_pow] \<turnstile> [Pred (\<lambda>s. s\<langle>''y''\<rangle> = 1) \<sqinter> Rel (Sb ''z'' (Num 1)) \<Zcat> \<mu> ''stat''. (Rel (R_stat ''z'') \<squnion> Rel (R_stat ''z'') \<Zcat> RVar ''stat'') \<squnion> Pred (\<lambda>s. s\<langle>''y''\<rangle> \<noteq> 1) \<sqinter> Pred (\<lambda>s. True) \<Zcat> Rel (R_change ''z'') \<Zcat> Pred (\<lambda>s. True)]"
  apply (simp add: S_pow_def)
  apply disj_r
  apply (tfi_case "(\<lambda>s. s\<langle>''y''\<rangle> = 1)")
   apply conj_r
    apply close
   apply (ch_upd rel)
   apply unfr
   apply disj_r
   apply (ch_id rel)
   apply (lenr 4)
   apply (fpi "(\<lambda>s. s\<langle>''y''\<rangle> = 1)")
   apply disj_l
    apply conj_l
    apply disj_r
    apply (ch_id rel)
    apply disj_r
    apply (ch_id rel)
    apply disj_r
    apply rel
   apply conj_l
   apply disj_r
   apply (ch_id rel)
   apply disj_r
   apply (ch_upd rel)
   apply disj_r
   apply (ch_id rel)
   apply unfl
   apply disj_r
   apply (ch_upd rel)
   apply disj_r
   apply (ch_id rel)
   apply rvar
  apply (rule CONJ_R[of "Pred (\<lambda>s. s\<langle>''y''\<rangle> \<noteq> 1)"], (auto)[1], simp)
   apply close
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply arb2
   apply (ch_id close)
   apply arb2
   apply (ch_id close)
   apply arb1
   apply end_upd
    prefer 2
    apply true
   prefer 2
   apply conj_l
   apply arb2
   apply (ch_id close)
   apply arb1
   apply (ch_upd rel)
   apply true
  oops

(* MA example 8.3 A, tfi *)
lemma "[stf S_pow] \<turnstile> [Pred (\<lambda>s. s\<langle>''y''\<rangle> = 1) \<sqinter> Rel (Sb ''z'' (Num 1)) \<Zcat> \<mu> ''stat''. (Rel (R_stat ''z'') \<squnion> Rel (R_stat ''z'') \<Zcat> RVar ''stat'') \<squnion> Pred (\<lambda>s. s\<langle>''y''\<rangle> \<noteq> 1) \<sqinter> Pred (\<lambda>s. True) \<Zcat> Rel (R_change ''z'') \<Zcat> Pred (\<lambda>s. True)]"
  apply (simp add: S_pow_def)
  apply disj_r
  apply (tfi_case "(\<lambda>s. s\<langle>''y''\<rangle> = 1)")
   apply tfi_auto
    apply (lenr 4)
    apply (fpi "(\<lambda>s. s\<langle>''y''\<rangle> = 1)")
    apply tfi_unf[1]
   apply tfi_auto
   apply (lenr 4)
   apply (fpi "(\<lambda>s. s\<langle>''y''\<rangle> = 1)")
   apply tfi_unf[1]
  apply tfi_auto
   prefer 2
   apply tfi_unf
   prefer 2
   apply tfi_auto
  oops

(* MA example 8.3 B as in MA*)
lemma "[stf S_pow] \<turnstile> [Rel (Sb ''z'' (Num 1)) \<Zcat> \<mu> ''zstat''. (Rel (R_stat ''z'') \<squnion> Rel (R_stat ''z'') \<Zcat> RVar ''zstat'') \<squnion> \<mu> ''xstat''. (Rel (R_stat ''x'') \<squnion> Rel (R_stat ''x'') \<Zcat> RVar ''xstat'') \<Zcat> Rel (R_change ''x'') \<Zcat> Pred (\<lambda>s. True)]"
  apply (simp add: S_pow_def)
  apply disj_r
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_upd \<open>close | rel\<close>)
  apply unfr
  apply ch_unfr
  apply disj_r
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_id rel)
  apply (tfi_case "(\<lambda>s. s\<langle>''x''\<rangle> = 1)")
   apply unfl
   apply disj_l
    apply conj_l
    apply unfr
    apply disj_r
    apply (ch_id rel)
    apply unfr
    apply disj_r
    apply (ch_id rel)
    apply unfr
    apply disj_r
    apply rel
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_id rel)
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_upd rel)
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_id rel)
  apply unfl
  apply (ch_upd rel)
  by true

(* MA example 8.3 B simplified *)
lemma "[stf S_pow] \<turnstile> [Rel (Sb ''z'' (Num 1)) \<Zcat> \<mu> ''zstat''. (Rel (R_stat ''z'') \<squnion> Rel (R_stat ''z'') \<Zcat> RVar ''zstat'') \<squnion> \<mu> ''xstat''. (Rel (R_stat ''x'') \<squnion> Rel (R_stat ''x'') \<Zcat> RVar ''xstat'') \<Zcat> Rel (R_change ''x'') \<Zcat> Pred (\<lambda>s. True)]"
  apply (simp add: S_pow_def)
  apply disj_r
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_upd \<open>close | rel\<close>)
  apply unfr
  apply ch_unfr
  apply disj_r
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_id rel)
  apply unfl
  apply disj_l
   apply conj_l
   apply unfr
   apply disj_r
   apply (ch_id rel)
   apply unfr
   apply disj_r
   apply (ch_id rel)
   apply unfr
   apply disj_r
   apply rel
  apply conj_l
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_id rel)
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_upd rel)
  apply ch_unfr
  apply ch_disj_r
  apply ch_ch_r
  apply (ch_id rel)
  apply unfl
  apply (ch_upd rel)
  by true

(* MA example 8.3 B, tfi *)
lemma "[stf S_pow] \<turnstile> [Rel (Sb ''z'' (Num 1)) \<Zcat> \<mu> ''zstat''. (Rel (R_stat ''z'') \<squnion> Rel (R_stat ''z'') \<Zcat> RVar ''zstat'') \<squnion> \<mu> ''xstat''. (Rel (R_stat ''x'') \<squnion> Rel (R_stat ''x'') \<Zcat> RVar ''xstat'') \<Zcat> Rel (R_change ''x'') \<Zcat> Pred (\<lambda>s. True)]"
  apply (simp add: S_pow_def)
  by tfi_unf

end