theory "Properties_Even"
  imports "../../TFI_Prover" "../../JC_Prover"
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

(* example 6 *)
(* If variable y initially set to 0,
   then y remains either 1 or 0 - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>e (''y'' := Num 0;;Call ''even'') : (\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin''))"
  apply (rule_tac \<phi>' = "stf(''y'' := Num 0, T\<^sub>e) \<Zcat> (Rel Id)
    \<Zcat> (\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin''))" in CONS)
  defer
  apply tfi_auto
  apply (simp add: T\<^sub>e_def)
  apply jc_auto+
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> (\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin''))")
  apply jc_auto
  apply (cons "stf(''y'' := Num 1, T\<^sub>e)")
  apply jc_auto
  apply auto
  apply unfr
  apply disj_r
  apply rel
  defer
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e)
    \<Zcat> (Rel Id) \<Zcat> (\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin''))")
  apply jc_auto+
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> (\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin''))")
  apply jc_auto
  apply (cons "stf(''y'' := Num 0, T\<^sub>e)")
  apply jc_auto
  apply auto
  apply unfr
  apply disj_r
  apply rel
  defer
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
    \<Zcat> (\<mu> ''bin''. (Rel R_y_bin \<squnion> Rel R_y_bin \<Zcat> RVar ''bin''))")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  apply auto
  prefer 3
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_ID, simp_all)
  defer
  apply close
  prefer 3
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_ID, simp_all)
  defer
  apply close
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_ID, simp_all)
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_UPD, simp_all+)
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_ID, simp_all)
  defer
  apply close
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_ID, simp_all)
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_UPD, simp_all+)
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')"
     and \<Psi>s = "[\<mu> ''bin''. (Rel R_y_bin \<squnion>
                  Rel R_y_bin \<Zcat>
                  RVar
                   ''bin'')]" in CH_ID, simp_all)
  defer
  apply close
  oops

(* example 7 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>e (Call ''even'') : (Rel Id \<Zcat>
    (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin))"
  apply (simp add: T\<^sub>e_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 1, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_y_bin]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin)")
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 0, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
    and \<Psi>s = "[Rel R_y_bin]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin)")
  apply jc_auto
    apply (simp add: sequent_valid_def)+
  apply auto
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_y_bin)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_y_bin)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "(Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_y_bin)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close
  apply disj_l
  defer
  apply close
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_y_bin)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_y_bin)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "(Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_y_bin)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close
  apply disj_l
  defer
  apply close
  apply arb1
  defer
  apply arb1
  oops

(* example 8 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 - PROVEN *)
lemma "[] \<turnstile>\<^sub>T\<^sub>e (Call ''even'') : (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin)"
  apply (rule_tac \<phi>' = "Rel Id \<Zcat> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin" in CONS)
  defer
  apply disj_r
  apply arb2
  apply close
  apply (simp add: T\<^sub>e_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 1, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_y_bin]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin")
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 0, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
    and \<Psi>s = "[Rel R_y_bin]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin")
  apply jc_auto
  apply (simp add: sequent_valid_def)+
  apply auto
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     Pred (\<lambda>s. True) \<Zcat>
     Rel R_y_bin"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     Pred (\<lambda>s. True) \<Zcat>
     Rel R_y_bin"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close+
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     Pred (\<lambda>s. True) \<Zcat>
     Rel R_y_bin"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     Pred (\<lambda>s. True) \<Zcat>
     Rel R_y_bin"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_y_bin]" in CH_ID, simp_all)
  by close+

(* example 9 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 once x reaches 0 - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>e (Call ''even'') : (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)"
    apply (rule_tac \<phi>' = "Rel Id \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)" in CONS)
  apply (simp add: T\<^sub>e_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 1, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)")
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 0, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)")
  apply jc_auto
    apply (simp add: sequent_valid_def)+
  apply auto
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "(Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply disj_l
  defer
  apply close
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "(Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply disj_l
  defer
  apply close
  apply tfi_auto
  apply arb1
  defer
  apply arb1
  defer
  apply arb1
  defer
  apply arb1
  oops

(* example 10 *)
(* If variable x not negative to begin with,
   then y eventually becomes 1 or 0 once x reaches 0 - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>e (Call ''even'') : (Rel Id \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale))"
  apply (simp add: T\<^sub>e_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 1, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 1))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)")
  apply jc_auto+
  apply (cons "stf(SKIP;;''y'' := Num 0, T\<^sub>e)")
  apply jc_auto
  apply simp
  apply disj_r+
  apply (rule_tac \<Phi> = "Rel (Sb ''y'' (Num 0))"
    and \<Psi>s = "[Rel R_finale]" in CH_ID, simp_all+)
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>e) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>e) \<Zcat> stf(SKIP, T\<^sub>e)
     \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Rel R_finale)")
  apply jc_auto
    apply (simp add: sequent_valid_def)+
  apply auto
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "(Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply disj_l
  defer
  apply close
  apply disj_r+
  apply arb2
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_UPD, simp_all+)
  apply close
  apply arb2
  apply (rule_tac \<Phi> = "(Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion>
      Pred (\<lambda>s. True) \<Zcat>
      Rel R_finale)"
    and \<Psi>s = "[Pred (\<lambda>s. True) \<Zcat> Rel R_finale]" in CH_ID, simp_all)
  apply close
  apply disj_l
  defer
  apply close
  apply arb1
  defer
  apply arb1
  oops

end