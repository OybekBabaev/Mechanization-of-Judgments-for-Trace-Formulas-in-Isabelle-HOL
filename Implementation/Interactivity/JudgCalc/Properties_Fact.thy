theory "Properties_Fact"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

definition R_x_inc :: "(state \<times> state) set" where
  [rels]: "R_x_inc \<equiv> {(s, s'). s\<langle>''x''\<rangle> \<le> s'\<langle>''x''\<rangle>}"

definition R_n_one :: "(state \<times> state) set" where
  [rels]: "R_n_one \<equiv> {(s, s'). s'\<langle>''n''\<rangle> \<ge> 1}"

definition R_combo :: "(state \<times> state) set" where
  [rels]: "R_combo \<equiv> R_x_inc \<inter> R_n_one"

type_synonym Tmap = "(method_name, S) fmap"

(* fact(), which is *)
(* if n \<le> 1 then skip else x := xn ; n := n - 1 ; fact() *)

definition T\<^sub>f :: Tmap where
  "T\<^sub>f = fmap_of_list [(''fact'', IF Leq (Var ''n'') (Num 1)
      THEN SKIP
      ELSE ''x'' := (Var ''x'' \<otimes> Var ''n'');;
        ''n'' := (Var ''n'' \<ominus> Num 1);;Call ''fact'' FI)]"

(* example 4 *)
(* Variable x never decreases throughout execution,
   provided x was positive to begin with - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>f (Call ''fact'') : (Pred (\<lambda>s. s\<langle>''x''\<rangle> \<le> 0) \<squnion> \<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc''))"
  apply (rule_tac \<phi>' = "(Rel Id) \<Zcat> (\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc''))" in CONS)
  defer
  apply tfi_auto
  apply (simp add: T\<^sub>f_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;SKIP, T\<^sub>d)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>f) \<Zcat> stf(''x'' := (Var ''x'' \<otimes> Var ''n''), T\<^sub>f)
    \<Zcat> stf(''n'' := (Var ''n'' \<ominus> Num 1), T\<^sub>f) \<Zcat> stf(SKIP, T\<^sub>f)
    \<Zcat> (\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc''))")
  apply jc_auto
  apply (simp_all add: sequent_valid_def)
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "stf(''x'' := (Var ''x'' \<otimes> Var ''n''), T\<^sub>f)
    \<Zcat> stf(''n'' := (Var ''n'' \<ominus> Num 1), T\<^sub>f) \<Zcat> stf(SKIP, T\<^sub>f)
    \<Zcat> (\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc''))"
    and \<Psi>s = "[\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')]" in CH_ID, simp_all)
  apply rel
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "stf(''n'' := (Var ''n'' \<ominus> Num 1), T\<^sub>f) \<Zcat> stf(SKIP, T\<^sub>f)
    \<Zcat> (\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc''))"
    and \<Psi>s = "[\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')]" in CH_UPD, simp_all+)
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "stf(SKIP, T\<^sub>f)
    \<Zcat> (\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc''))"
    and \<Psi>s = "[\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')]" in CH_UPD, simp_all+)
  apply rel
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')"
    and \<Psi>s = "[\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')]" in CH_ID, simp_all)
  apply rel
  apply close
  oops

(* example 5 *)
(* Variable x never decreases throughout execution
   and variable n stays gte 1,
   provided x was positive to begin with - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>f (''n'' := Num 10;;Call ''fact'') : (Pred (\<lambda>s. s\<langle>''x''\<rangle> \<le> 0) \<squnion> \<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo''))"
  apply (cons "stf(''n'' := Num 10, T\<^sub>f) \<Zcat> Rel Id \<Zcat> (\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo''))")
  apply jc_auto
  apply (simp add: T\<^sub>f_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;SKIP, T\<^sub>d)")
  apply jc_auto
  apply simp
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel Id"
      and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_ID)
  apply simp_all
  prefer 3
  apply (cons "stf(SKIP, T\<^sub>f) \<Zcat> stf(''x'' := (Var ''x'' \<otimes> Var ''n''), T\<^sub>f)
    \<Zcat> stf(''n'' := (Var ''n'' \<ominus> Num 1), T\<^sub>f) \<Zcat> stf(SKIP, T\<^sub>f)
    \<Zcat> (\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo''))")
  apply jc_auto
  apply (simp add: sequent_valid_def)+
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<otimes> Var ''n'')) \<Zcat>
     Rel (Sb ''n'' (Var ''n'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')"
      and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_ID)
  apply simp_all
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''n'' (Var ''n'' \<ominus> Num 1)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')"
      and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_UPD)
  apply simp_all+
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')"
      and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_UPD)
  apply simp_all+
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')"
      and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_ID)
  apply simp_all
  defer
  apply close
  prefer 3
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel Id
    \<Zcat> (\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo''))"
    and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_UPD, simp_all+)
  apply rel
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')"
    and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]" in CH_ID, simp_all)
  apply rel
  apply close
  oops

end