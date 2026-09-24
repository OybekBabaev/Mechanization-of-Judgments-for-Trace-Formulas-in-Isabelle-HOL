theory "Example_Power"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

type_synonym Tmap = "(method_name, S) fmap"

(* power(), which is *)
(* if x = 1 then skip else z := zy ; subtract() *)
(* subtract(), which is *)
(* x := x - 1 ; power() *)

definition T\<^sub>3 :: Tmap where
  "T\<^sub>3 = fmap_of_list [(''power'', IF Eq (Var ''x'') (Num 1)
    THEN SKIP ELSE ''z'' := (Var ''z'' \<otimes> Var ''y'');;Call ''subtract'' FI),
    (''subtract'', ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''power'')]"

lemma "[] \<turnstile>\<^sub>T\<^sub>3 (''z'' := Num 1;;Call ''power'') : Rel (Sb ''z'' (Num 1)) \<Zcat> stf(Call ''power'', T\<^sub>3)"
  apply (simp add: T\<^sub>3_def)
  apply (seq, assign)
  apply call
  apply unfold
  apply ite
  apply (rule_tac \<phi>' = "stf(SKIP;;SKIP, T\<^sub>3)" in CONS, simp)
  apply (seq, skip, skip)
  apply tfi_auto
  apply (rule_tac \<phi>' = "stf(SKIP, T\<^sub>3) \<Zcat> stf(''z'' := (Var ''z'' \<otimes> Var ''y''), T\<^sub>3)
    \<Zcat> stf(Call ''subtract'', fmap_of_list [(''power'', IF Eq (Var ''x'') (Num 1)
    THEN SKIP ELSE ''z'' := (Var ''z'' \<otimes> Var ''y'');;Call ''subtract'' FI),
    (''subtract'', ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''power'')])" in CONS, simp)
  apply (seq, skip)
  apply (seq, assign)
  apply call
  apply unfold
  apply (seq, assign)
  apply (rule_tac \<phi>' = "stf(Call ''power'', fmap_of_list [(''power'', IF Eq (Var ''x'') (Num 1)
    THEN SKIP ELSE ''z'' := (Var ''z'' \<otimes> Var ''y'');;Call ''subtract'' FI),
    (''subtract'', ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''power'')])" in CONS, simp)
  apply (seq, skip)
  apply (simp add: sequent_valid_def)
  apply blast
  apply tfi_auto
  apply (rule FPI_ALT)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1)" and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
   Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                     Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                               Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat> RVar ''power'')"
      and \<Psi>s = "[Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
        Rel Trace_Formulas.Id \<Zcat>
          \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                     Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat> RVar ''power'')"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
        \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                     Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    RVar
     ''power'')"
       and \<Psi>s = "[\<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                       Rel Trace_Formulas.Id \<Zcat>
                                       \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
         Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
         Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
         Rel Trace_Formulas.Id \<Zcat>
         Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))]" in CH_ID, simp_all)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''power''"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
        \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter> Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
               Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
               Rel Trace_Formulas.Id \<Zcat>
               Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
               Rel Trace_Formulas.Id \<Zcat>
               \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
              Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
            Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
   Rel Trace_Formulas.Id \<Zcat>
   Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat> RVar ''subtract'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''power''"
      and \<Psi>s = "[\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                 Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                 Rel Trace_Formulas.Id \<Zcat>
                 Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                 Rel Trace_Formulas.Id \<Zcat>
                 \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                   Rel Trace_Formulas.Id \<Zcat>
                                   \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat> RVar ''subtract'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''power''" in RVAR)
  apply auto
  apply disj_r
  apply disj_r
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
              Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
              Rel Trace_Formulas.Id \<Zcat>
              \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
  Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
  Rel Trace_Formulas.Id \<Zcat>
  Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
  Rel Trace_Formulas.Id \<Zcat>
  \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat> RVar ''power'')))" in CONJ_R, simp_all)
  apply tfi_auto
  apply (rule FPI_ALT)
  apply auto
  apply (rule UNFR)
  apply auto
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply tfi_auto
  apply (rule FPI_ALT)
  apply auto
  apply (rule UNFR)
  apply auto
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  by tfi_auto

(* the same, but with new proof automation *)

lemma "[] \<turnstile>\<^sub>T\<^sub>3 (''z'' := Num 1;;Call ''power'') : Rel (Sb ''z'' (Num 1)) \<Zcat> stf(Call ''power'', T\<^sub>3)"
  apply (simp add: T\<^sub>3_def)
  apply jc_auto
  apply call
  apply unfold
  apply jc_auto
  apply (cons "stf(SKIP;;SKIP, T\<^sub>3)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>3) \<Zcat> stf(''z'' := (Var ''z'' \<otimes> Var ''y''), T\<^sub>3)
    \<Zcat> stf(Call ''subtract'', fmap_of_list [(''power'', IF Eq (Var ''x'') (Num 1)
    THEN SKIP ELSE ''z'' := (Var ''z'' \<otimes> Var ''y'');;Call ''subtract'' FI),
    (''subtract'', ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''power'')])")
  apply jc_auto
  apply call
  apply unfold
  apply seq
  apply assign
  apply (cons "stf(Call ''power'', fmap_of_list [(''power'', IF Eq (Var ''x'') (Num 1)
    THEN SKIP ELSE ''z'' := (Var ''z'' \<otimes> Var ''y'');;Call ''subtract'' FI),
    (''subtract'', ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''power'')])")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  apply auto
  apply tfi_auto
  apply (rule FPI_ALT)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1)" and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
   Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                     Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                               Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat> RVar ''power'')"
      and \<Psi>s = "[Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
        Rel Trace_Formulas.Id \<Zcat>
          \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                     Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat> RVar ''power'')"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
        \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                     Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    RVar
     ''power'')"
       and \<Psi>s = "[\<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                       Rel Trace_Formulas.Id \<Zcat>
                                       \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
         Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
         Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
         Rel Trace_Formulas.Id \<Zcat>
         Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''subtract''))]" in CH_ID, simp_all)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''power''"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
        \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter> Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
               Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
               Rel Trace_Formulas.Id \<Zcat>
               Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
               Rel Trace_Formulas.Id \<Zcat>
               \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
              Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
            Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
   Rel Trace_Formulas.Id \<Zcat>
   Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat> RVar ''subtract'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''power''"
      and \<Psi>s = "[\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                 Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                 Rel Trace_Formulas.Id \<Zcat>
                 Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                 Rel Trace_Formulas.Id \<Zcat>
                 \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                   Rel Trace_Formulas.Id \<Zcat>
                                   \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat> RVar ''subtract'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''power''" in RVAR)
  apply auto
  apply disj_r
  apply disj_r
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
              Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
              Rel Trace_Formulas.Id \<Zcat>
              \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
  Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
  Rel Trace_Formulas.Id \<Zcat>
  Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
  Rel Trace_Formulas.Id \<Zcat>
  \<mu> ''subtract''. (Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat> RVar ''power'')))" in CONJ_R, simp_all)
  apply tfi_auto
  apply (rule FPI_ALT)
  apply auto
  apply (rule UNFR)
  apply auto
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply tfi_auto
  apply (rule FPI_ALT)
  apply auto
  apply (rule UNFR)
  apply auto
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                     \<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
          Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
          Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
          Rel Trace_Formulas.Id \<Zcat>
          RVar ''subtract'')"
    and \<Psi>s = "[\<mu> ''power''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''z'' (Var ''z'' \<otimes> Var ''y'')) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''subtract''. (Rel
          (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
         Rel Trace_Formulas.Id \<Zcat> RVar ''power''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  by tfi_auto

end