theory "Properties_Down"
  imports "../../TFI_Prover"
begin

definition R_x_dec :: "(state \<times> state) set" where
  [rels]: "R_x_dec \<equiv> {(s, s'). s\<langle>''x''\<rangle> \<ge> s'\<langle>''x''\<rangle>}"

type_synonym Tmap = "(method_name, S) fmap"

(* down(), which is *)
(* if x == 0 then skip else x := x - 1 ; down() *)

definition T\<^sub>d :: Tmap where
  "T\<^sub>d = fmap_of_list [(''down'', IF Eq (Var ''x'') (Num 0)
        THEN SKIP ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''down'' FI)]"

definition Rec_down :: Rec where
  "Rec_down \<equiv> (Call ''down'', T\<^sub>d)"

(* example 1 *)
(* Variable x never increases throughout execution - PROVEN *)
lemma "[stf Rec_down] \<turnstile> [\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec'')]"
  apply (simp add: Rec_down_def T\<^sub>d_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. True")
  by tfi_auto

(* example 2 *)
(* If variable x not negative to begin with, then call terminates - PROVEN *)
lemma "[stf Rec_down] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0)]"
  apply (simp add: Rec_down_def T\<^sub>d_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. s\<langle>''x''\<rangle> \<ge> 0")
  by tfi_auto

end