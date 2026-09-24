theory "Properties_Power"
  imports "../../TFI_Prover"
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

definition Rec_power :: Rec where
  "Rec_power \<equiv> (Call ''power'', T\<^sub>3)"

(* example 3 *)
(* Variable x never increases throughout execution - PROVEN *)
lemma "[stf Rec_power] \<turnstile> [\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]"
  apply (simp add: Rec_power_def T\<^sub>3_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  by tfi_auto

end