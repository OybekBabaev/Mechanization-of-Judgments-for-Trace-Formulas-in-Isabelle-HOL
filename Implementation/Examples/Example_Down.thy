theory Example_Down
  imports "../TFI_Prover"
begin

definition Rec_down :: Rec where
  "Rec_down \<equiv> (Call ''down'',
               fmap_of_list [(''down'', IF Var ''x'' == Num 0
                                        THEN ''x'' := Var ''x'' \<ominus> Num 1
                                        ELSE ''x'' := Var ''x'' \<ominus> Num 2;;
                                             Call ''down'' FI)])"

definition \<Phi>_down :: trace_formula where
  "\<Phi>_down \<equiv> Rel Id \<Zcat> \<mu> ''down''. 
      (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter> Rel Id \<Zcat> Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter> Rel Id \<Zcat> Rel (Sb ''x'' (Var ''x'' \<ominus> Num 2)) \<Zcat> 
                                 Rel Id \<Zcat> RVar ''down'')"

lemma "stf Rec_down = \<Phi>_down"
  by (simp add: Rec_down_def \<Phi>_down_def)

definition R_x_dec :: "(state \<times> state) set" where
  [rels]: "R_x_dec \<equiv> {(s, s'). s\<langle>''x''\<rangle> \<ge> s'\<langle>''x''\<rangle>}"

(* MA appendix example 8.1A *)
lemma "[stf Rec_down] \<turnstile> [\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]"
  apply (simp add: Rec_down_def)
  apply unfr
  apply disj_r
  apply (ch_id rel)
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
   apply unfr
   apply disj_r
   apply conj_l
   apply (ch_id rel)
   apply unfr
   apply disj_r
   apply rel
  apply unfr
  apply disj_r
  apply conj_l
  apply (ch_id rel)
  apply unfr
  apply disj_r
  apply (ch_upd rel)
  apply unfr
  apply disj_r
  apply (ch_id rel)
  by rvar

(* MA appendix example 8.1A, tfi_methods*)
lemma "[stf Rec_down] \<turnstile> [\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]"
  apply (simp add: Rec_down_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  by tfi_auto

(*MA appendix example 8.1B*)
lemma "[stf Rec_down] \<turnstile> [\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]"
  apply (simp add: Rec_down_def)
  apply unfr
  apply disj_r
  apply (ch_id rel)
  apply (lenr 2)
  apply (fpi "\<lambda>s. True")
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
  apply (ch_id rel)
  by rvar

(*MA appendix example 8.1B, tfi_methods *)
lemma "[stf Rec_down] \<turnstile> [\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]"
  apply (simp add: Rec_down_def)
  apply tfi_auto
  apply (lenr 2)
  apply (fpi "\<lambda>s. True")
  by tfi_auto

(* MA example 8.1 C *)
lemma "[stf Rec_down] \<turnstile> [Pred (\<lambda>s. \<not> (\<exists>k. s\<langle>''x''\<rangle> = 2 * k)) \<squnion> Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = -1)]"
  apply (simp add: Rec_down_def)
  apply disj_r
  apply (tfi_case "(\<lambda>s. \<forall>k. s\<langle>''x''\<rangle> \<noteq> 2 * k)")
  apply close
  apply disj_r
  apply (tfi_case "(\<lambda>s. s\<langle>''x''\<rangle> < 0)")
  apply close
  apply arb2
  apply (ch_id close)
  apply (fpi_alt "\<lambda>s. (\<exists>k. s\<langle>''x''\<rangle> = 2 * k) \<and> s\<langle>''x''\<rangle> \<ge> 0")
  apply disj_l
   apply conj_l
   apply arb1
   apply ch_predr
   apply arb2
   apply (ch_id close)
   apply end_upd
    apply true
   apply close
  apply conj_l
  apply arb2
  apply (ch_id close)
  apply arb2
  apply (ch_upd close)
  apply arb2
  apply (ch_id close)
  apply rvar
  by presburger

(* MA example 8.1 C,  tfi *)
lemma "[stf Rec_down] \<turnstile> [Pred (\<lambda>s. \<not> (\<exists>k. s\<langle>''x''\<rangle> = 2 * k)) \<squnion> Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = -1)]"
  apply (simp add: Rec_down_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. (\<exists>k. s\<langle>''x''\<rangle> = 2 * k) \<and> s\<langle>''x''\<rangle> \<ge> 0")
  apply tfi_auto
  by presburger

end