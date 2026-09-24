theory "Properties_NonTail"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

definition R_x_dec :: "(state \<times> state) set" where
  [rels]: "R_x_dec \<equiv> {(s, s'). s\<langle>''x''\<rangle> \<ge> s'\<langle>''x''\<rangle>}"

definition R_y_inc :: "(state \<times> state) set" where
  [rels]: "R_y_inc \<equiv> {(s, s'). s\<langle>''y''\<rangle> \<le> s'\<langle>''y''\<rangle>}"

type_synonym Tmap = "(method_name, S) fmap"

(* nt(), which is *)
(* if x \<le> 0 then skip else x := x - 1 ; nt() ; y := y + 1 *)

definition T\<^sub>t :: Tmap where
  "T\<^sub>t = fmap_of_list [(''nt'', IF Leq (Var ''x'') (Num 0)
        THEN SKIP
        ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;
              (Call ''nt'');;''y'' := (Var ''y'' \<oplus> Num 1) FI)]"

(* example 11 *)
(* Variable x never increases throughout execution - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>t (Call ''nt'') : (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))"
  apply (rule_tac \<phi>' = "Rel Id \<Zcat> \<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')" in CONS)
  apply (rule CALL)
  apply (simp_all add: T\<^sub>t_def)+
  apply jc_auto
  apply (cons "stf(SKIP;;SKIP, T\<^sub>t)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>t) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>t)
    \<Zcat> (stf(SKIP, T\<^sub>t) \<Zcat> \<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))
    \<Zcat> stf(''y'' := (Var ''y'' \<oplus> Num 1), T\<^sub>t)")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  apply jc_auto
  apply simp
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     (Rel Trace_Formulas.Id \<Zcat> \<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')) \<Zcat>
     Rel (Sb ''y''
           (Var ''y'' \<oplus>
            Num 1))" and \<Psi>s = "[\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]" in CH_ID)
  apply simp_all
  apply rel
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "(Rel Trace_Formulas.Id \<Zcat> \<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')) \<Zcat>
     Rel (Sb ''y''
           (Var ''y'' \<oplus>
            Num 1))" and \<Psi>s = "[\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]" in CH_UPD)
  apply simp_all+
  apply rel
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')" and \<Psi>s = "[\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]" in CH_ID)
  apply simp_all
  apply rel
  apply close
  apply tfi_auto (*CH-DISJ-L must have been applied here *)
  oops

(* example 12 *)
(* Variable y never decreases throughout execution - ABANDONED *)
lemma "[] \<turnstile>\<^sub>T\<^sub>t (Call ''nt'') : (\<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc''))"
  apply (rule_tac \<phi>' = "Rel Id \<Zcat> \<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')" in CONS)
  apply (rule CALL)
  apply (simp_all add: T\<^sub>t_def)+
  apply jc_auto
  apply (cons "stf(SKIP;;SKIP, T\<^sub>t)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>t) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>t)
    \<Zcat> (stf(SKIP, T\<^sub>t) \<Zcat> \<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc''))
    \<Zcat> stf(''y'' := (Var ''y'' \<oplus> Num 1), T\<^sub>t)")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  apply jc_auto
  apply simp
  defer
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "\<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')" and \<Psi>s = "[\<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')]" in CH_ID)
  apply simp_all
  apply rel
  apply close
  apply disj_r
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat>
     (Rel Trace_Formulas.Id \<Zcat> \<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')) \<Zcat>
     Rel (Sb ''y''
           (Var ''y'' \<oplus>
            Num 1))" and \<Psi>s = "[\<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')]" in CH_ID)
  apply simp_all
  apply rel
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "(Rel Trace_Formulas.Id \<Zcat> \<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')) \<Zcat>
     Rel (Sb ''y''
           (Var ''y'' \<oplus>
            Num 1))" and \<Psi>s = "[\<mu> ''inc''. (Rel R_y_inc \<squnion> Rel R_y_inc \<Zcat> RVar ''inc'')]" in CH_UPD)
  apply simp_all+
  apply rel
  apply tfi_auto (* CH-DISJ-L must have been used here *)
  oops

end