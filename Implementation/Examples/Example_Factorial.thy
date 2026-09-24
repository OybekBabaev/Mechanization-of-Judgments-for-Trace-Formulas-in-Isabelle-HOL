theory Example_Factorial
  imports "../TFI_Prover"
begin

notation fmap_of_list ("fm")

(* MA example in 3.1*)
definition factorial :: Rec where 
"factorial \<equiv> (''x'' := Num 10;;
              ''y'' := Num 1;;
              Call ''fac'',
fm [(''fac'', IF (Var ''x'' == Num 1)
              THEN SKIP
              ELSE ''y'' := Var ''y'' \<otimes> Var ''x'';;
                   ''x'' := Var ''x'' \<ominus> Num 1;;
                   Call ''fac'' FI)])"

definition R_y_inc :: "(state \<times> state) set" where
  "R_y_inc \<equiv> {(s, s'). s\<langle>''y''\<rangle> \<le> s'\<langle>''y''\<rangle>}"

declare R_y_inc_def [rels]

lemma "[stf factorial] \<turnstile> [Rel (Sb ''x'' (Num 10)) \<Zcat> Rel (Sb ''y'' (Num 1)) \<Zcat> \<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')]"
  apply (simp add: factorial_def)
  apply (ch_upd close)
  apply (ch_upd close)
  apply unfr
  apply disj_r
  apply (ch_id rel)
  apply (lenr 3)
  apply (fpi "\<lambda>s. s\<langle>''x''\<rangle> \<ge> 1 \<and> s\<langle>''y''\<rangle> \<ge> 1")
  apply disj_l
   apply disj_r
   apply conj_l
   apply (ch_id rel)
   apply disj_r
   apply rel
  apply disj_r
  apply conj_l
  apply (ch_id rel)
  apply disj_r
  apply (ch_upd rel)
  apply disj_r
  apply (ch_upd rel)
  apply disj_r
  apply (ch_id rel)
  apply rvar
  by (simp add: int_one_le_iff_zero_less)

(* MA example in 3.1 (with tfi_methods) *)
lemma "[stf factorial] \<turnstile> [Rel (Sb ''x'' (Num 10)) \<Zcat> Rel (Sb ''y'' (Num 1)) \<Zcat> \<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')]"
  apply (simp add: factorial_def)
  apply tfi_auto
  apply (lenr 3)
  apply (fpi "\<lambda>s. s\<langle>''x''\<rangle> \<ge> 1 \<and> s\<langle>''y''\<rangle> \<ge> 1")
  apply tfi_auto
  by (simp add: int_one_le_iff_zero_less)

(* MA example 8.2 *)
lemma "[stf factorial] \<turnstile> [Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''y''\<rangle> = 3628800)]"
  apply (simp add: factorial_def)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply unfl
  apply disj_l
   apply conj_l
   apply (pred "\<lambda>s. False")
   apply false
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_upd close)
  apply arb1
  apply (pred "(\<lambda>s. s\<langle>''y''\<rangle> = 3628800)")
  by close

(* MA example 8.2, tfi *)
lemma "[stf factorial] \<turnstile> [Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''y''\<rangle> = 3628800)]"
  apply (simp add: factorial_def)
  by (tfi_unf | pred "\<lambda>s. False")+

end