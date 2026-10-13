theory "Properties_Even"
  imports "../../TFI_Prover"
begin

definition R_y_bin :: "(state \<times> state) set" where
  [rels]: "R_y_bin \<equiv> {(s, s'). s'\<langle>''y''\<rangle> = 1 \<or> s'\<langle>''y''\<rangle> = 0}"

definition R_finale :: "(state \<times> state) set" where
  [rels]: "R_finale \<equiv> {(s, s'). s'\<langle>''x''\<rangle> = 0 \<longrightarrow> s'\<langle>''y''\<rangle> = 1 \<or> s'\<langle>''y''\<rangle> = 0}"

type_synonym Tmap = "(method_name, S) fmap"

(* even(), which is *)
(* if x == 0 then y := 1 else x := x - 1 ; odd() *)
(* odd(), which is *)
(* if x == 0 then y := 0 else x := x - 1 ; even() *)

definition T\<^sub>e :: Tmap where
  "T\<^sub>e = fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))]"

definition Rec_even :: Rec where
  "Rec_even \<equiv> (Call ''even'', T\<^sub>e)"

definition Rec_even_from_zero :: Rec where
  "Rec_even_from_zero \<equiv> (''y'' := Num 0;;Call ''even'', T\<^sub>e)"

(* example 6 *)
(* If variable y initially set to 0,
   then y remains either 1 or 0 - PROVEN *)
lemma "[stf Rec_even_from_zero] \<turnstile> [\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin'')]"
  apply (simp add: Rec_even_from_zero_def T\<^sub>e_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. s\<langle>''y''\<rangle> = 0")
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. s\<langle>''y''\<rangle> = 0")
  by tfi_auto

(* example 7 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 - PROVEN *)
lemma "[stf Rec_even] \<turnstile> [Rel Id \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin)]"
  apply (simp add: Rec_even_def T\<^sub>e_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_y_bin]" in CH_ID)
  apply simp+
  apply close
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                       Rel Trace_Formulas.Id \<Zcat>
                       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply close
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
      and \<Psi>s = "[Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply true
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                       Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  by tfi_auto

(* example 8 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 - PROVEN *)
lemma "[stf Rec_even] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]"
  apply (simp add: Rec_even_def T\<^sub>e_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_y_bin]" in CH_ID)
  apply simp+
  apply close
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                       Rel Trace_Formulas.Id \<Zcat>
                       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                       \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                    Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                    Rel Trace_Formulas.Id \<Zcat>
                                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                    Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply close
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
      and \<Psi>s = "[Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply true
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                       Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID)
  apply simp_all
  by tfi_auto

(* example 9 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 once x reaches 0 - PROVEN *)
lemma "[stf Rec_even] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale]"
  apply (simp add: Rec_even_def T\<^sub>e_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID)
  apply simp_all
  apply true
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                        Rel Trace_Formulas.Id \<Zcat>
                        \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat>
                                     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                     Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                        \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat>
                                     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                     Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat>
                                     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                     Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  apply close
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID)
  apply simp_all
  apply true
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                        Rel Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  by tfi_auto

(* example 10 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 once x reaches 0 - PROVEN *)
lemma "[stf Rec_even] \<turnstile> [Rel Id \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)]"
  apply (simp add: Rec_even_def T\<^sub>e_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID)
  apply simp_all
  apply true
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                        Rel Trace_Formulas.Id \<Zcat>
                        \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat>
                                     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                     Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
                        \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat>
                                     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                     Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "\<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                     Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter>
                                     Rel Trace_Formulas.Id \<Zcat>
                                     Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                                     Rel Trace_Formulas.Id \<Zcat> RVar ''even'')"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  apply close
  apply (fpi_alt "\<lambda>s. True")
  apply disj_l
  apply conj_l
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID)
  apply simp_all
  apply true
  apply rel
  apply conj_l
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
                        Rel Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Id \<Zcat> RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD)
  apply simp_all+
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "RVar ''even''"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID)
  apply simp_all
  by tfi_auto

end