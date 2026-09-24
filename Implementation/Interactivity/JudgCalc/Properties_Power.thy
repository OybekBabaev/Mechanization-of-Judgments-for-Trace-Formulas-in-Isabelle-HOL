theory "Properties_Power"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

definition R_x_dec :: "(state \<times> state) set" where
  [rels]: "R_x_dec \<equiv> {(s, s'). s\<langle>''x''\<rangle> \<ge> s'\<langle>''x''\<rangle>}"

type_synonym Tmap = "(method_name, S) fmap"

(* power(), which is *)
(* if x == 1 then skip else z := zy ; subtract() *)
(* subtract(), which is *)
(* x := x - 1 ; power() *)

definition T\<^sub>3 :: Tmap where
  "T\<^sub>3 = fmap_of_list [(''power'', IF Eq (Var ''x'') (Num 1)
    THEN SKIP ELSE ''z'' := (Var ''z'' \<otimes> Var ''y'');;Call ''subtract'' FI),
    (''subtract'', ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''power'')]"

(* example 3 *)
(* Variable x never increases throughout execution - PROVEN *)
lemma "[] \<turnstile>\<^sub>T\<^sub>3 (Call ''power'') : (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))"
  apply (rule_tac \<phi>' = "(Rel Id) \<Zcat> (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))" in CONS)
  defer
  apply tfi_auto
  apply (simp add: T\<^sub>3_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;SKIP, T\<^sub>3)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>3) \<Zcat> stf(''z'' := (Var ''z'' \<otimes> Var ''y''), T\<^sub>3)
    \<Zcat> (Rel Id) \<Zcat> (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))")
  apply jc_auto+
  apply (cons "stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>3) \<Zcat> stf(SKIP, T\<^sub>3)
   \<Zcat> (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  apply auto
  by tfi_auto

end