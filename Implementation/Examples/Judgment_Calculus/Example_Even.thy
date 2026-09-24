theory "Example_Even"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

type_synonym Tmap = "(method_name, S) fmap"

(* even(), which is *)
(* if x = 0 then y := 1 else x := x - 1 ; odd() *)
(* odd(), which is *)
(* if x = 0 then y := 0 else x := x - 1 ; even() *)

definition T\<^sub>e :: Tmap where
  "T\<^sub>e = fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))]"

lemma "[] \<turnstile>\<^sub>T\<^sub>e (Call ''even'') : stf(Call ''even'', T\<^sub>e)"
  apply (simp add: T\<^sub>e_def)
  apply call
  apply unfold
  apply ite
  apply (rule_tac \<phi>' = "stf(SKIP ;; ''y'' := Num 1, T\<^sub>e)" in CONS, simp)
  apply (seq, skip, assign)
  apply tfi_auto
  apply (rule_tac \<phi>' = "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>e)
    \<Zcat> stf(Call ''odd'', fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))])" in CONS, simp)
  apply (seq, skip)
  apply (seq, assign)
  apply call
  apply unfold
  apply ite
  apply (rule_tac \<phi>' = "stf(SKIP ;; ''y'' := Num 0, T\<^sub>e)" in CONS, simp)
  apply (seq, skip, assign)
  apply tfi_auto
  apply (rule_tac \<phi>' = "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>e)
    \<Zcat> stf(Call ''even'', fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))])" in CONS, simp)
  apply (seq, skip)
  apply (seq, assign)
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
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
        and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
        and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
        and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''even''"
       and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''even''" in RVAR)
  apply auto
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                               Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                               Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                               Rel Trace_Formulas.Id \<Zcat>
                               Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                               Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
Rel Trace_Formulas.Id \<Zcat>
Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat> Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply tfi_auto
  apply (rule FPI_ALT, auto)
  apply (rule UNFR, auto)
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
       and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
       and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
       and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''even''"
       and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''even''" in RVAR)
  apply auto
  apply disj_r
  apply disj_r
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
  and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
   Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))" in CONJ_R, simp+)
  apply tfi_auto
  apply (rule FPI_ALT, auto)
  apply (rule UNFR, auto)
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''odd''"
    and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''odd''" in RVAR)
  apply auto
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                RVar
                                 ''odd''))"
    and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                RVar
                                 ''odd''))"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                RVar
                                 ''odd''))"
    and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule FPI_ALT, auto)
  apply (rule UNFR, auto)
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''odd''"
    and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''odd''" in RVAR)
  by auto

(* the same, but with new proof automation *)

lemma "[] \<turnstile>\<^sub>T\<^sub>e (Call ''even'') : stf(Call ''even'', T\<^sub>e)"
  apply (simp add: T\<^sub>e_def)
  apply jc_auto
  apply unfold
  apply jc_auto
  apply (cons "stf(SKIP ;; ''y'' := Num 1, T\<^sub>e)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>e)
    \<Zcat> stf(Call ''odd'', fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))])")
  apply jc_auto
  apply call
  apply unfold
  apply jc_auto
  apply (cons "stf(SKIP ;; ''y'' := Num 0, T\<^sub>e)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>e)
    \<Zcat> stf(Call ''even'', fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))])")
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
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
        and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
        and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
        and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''even''"
       and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''even''" in RVAR)
  apply auto
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                               Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                               Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                               Rel Trace_Formulas.Id \<Zcat>
                               Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                               Rel Trace_Formulas.Id \<Zcat>
                               \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
        Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
          Rel Trace_Formulas.Id \<Zcat>
            Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat> Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply tfi_auto
  apply (rule FPI_ALT, auto)
  apply (rule UNFR, auto)
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
      and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
       and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
       and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
       and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
    Rel Trace_Formulas.Id \<Zcat>
    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
    Rel Trace_Formulas.Id \<Zcat>
    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
       and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''even''"
       and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
       Rel Trace_Formulas.Id \<Zcat>
       Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
       Rel Trace_Formulas.Id \<Zcat>
       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                  Rel Trace_Formulas.Id \<Zcat>
                                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                  Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''even''" in RVAR)
  apply auto
  apply disj_r
  apply disj_r
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
  and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
   Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))" in CONJ_R, simp+)
  apply tfi_auto
  apply (rule FPI_ALT, auto)
  apply (rule UNFR, auto)
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''odd''"
    and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''odd''" in RVAR)
  apply auto
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                RVar
                                 ''odd''))"
    and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
   Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                RVar
                                 ''odd''))"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
   \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat>
                  \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                Rel Trace_Formulas.Id \<Zcat>
                                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                Rel Trace_Formulas.Id \<Zcat>
                                RVar
                                 ''odd''))"
    and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                Rel Trace_Formulas.Id \<Zcat>
                Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                Rel Trace_Formulas.Id \<Zcat>
                \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                              Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                              Rel Trace_Formulas.Id \<Zcat>
                              Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                              Rel Trace_Formulas.Id \<Zcat>
                              \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''y'' (Num 0)) \<squnion>
                                           Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                           Rel Trace_Formulas.Id \<Zcat>
                                           Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                           Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule FPI_ALT, auto)
  apply (rule UNFR, auto)
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                   \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                    \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''odd'')"
      and \<Psi>s = "[\<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
     Rel Trace_Formulas.Id \<Zcat>
     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                  Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                  Rel Trace_Formulas.Id \<Zcat>
                  Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                  Rel Trace_Formulas.Id \<Zcat> RVar ''even''))]" in CH_ID, simp_all+)
  apply close
  apply (rule UNFL)
  apply auto
  apply (rule UNFR)
  apply auto
  apply disj_r
  apply disj_l
  apply close
  apply (rule CONJ_L, auto)
  apply (rule_tac \<Psi>\<^sub>1 = "Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0)"
    and \<Psi>\<^sub>2 = "Rel Trace_Formulas.Id \<Zcat>
                                      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))" in CONJ_R, simp+)
  apply (rule CLOSE, simp+)
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                      Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''odd''"
    and \<Psi>s = "[Rel Trace_Formulas.Id \<Zcat>
                                      \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_UPD, simp_all+)
  apply close
  apply (rule_tac \<Phi> = "RVar ''odd''"
    and \<Psi>s = "[\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
      Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
      Rel Trace_Formulas.Id \<Zcat>
      Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
      Rel Trace_Formulas.Id \<Zcat>
      \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                    Rel Trace_Formulas.Id \<Zcat>
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                    Rel Trace_Formulas.Id \<Zcat>
                    \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                 Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                 Rel Trace_Formulas.Id \<Zcat>
                                 Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                 Rel Trace_Formulas.Id \<Zcat> RVar ''even'')))]" in CH_ID, simp_all+)
  apply close
  apply (rule_tac X = "''odd''" in RVAR)
  by auto

end