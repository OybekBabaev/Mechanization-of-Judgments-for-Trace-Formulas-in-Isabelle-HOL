theory "Example_Down"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

type_synonym Tmap = "(method_name, S) fmap"

(* down(), which is *)
(* if x = 0 then skip else x := x - 1 ; down() *)

definition T\<^sub>d :: Tmap where
  "T\<^sub>d = fmap_of_list [(''down'', IF Eq (Var ''x'') (Num 0)
        THEN SKIP ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;(Call ''down'') FI)]"

lemma "[] \<turnstile>\<^sub>T\<^sub>d (Call ''down'') : stf(Call ''down'', T\<^sub>d)"
  apply (simp add: T\<^sub>d_def)
  apply call
  apply unfold
  apply ite
  apply (rule_tac \<phi>' = "stf(SKIP;;SKIP, T\<^sub>d)" in CONS, simp)
  apply seq
  apply skip
  apply skip
  apply tfi_auto
  apply (rule_tac \<phi>' = "stf(SKIP, T\<^sub>d) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>d)
     \<Zcat> stf(Call ''down'', fmap_of_list [(''down'', IF Eq (Var ''x'') (Num 0)
        THEN SKIP ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;(Call ''down'') FI)])" in CONS, simp)
  apply auto
  apply seq
  apply skip
  apply seq
  apply assign
  apply seq
  apply skip
  apply (simp add: sequent_valid_def)
  by tfi_auto

(* the same, but with new proof automation *)

lemma "[] \<turnstile>\<^sub>T\<^sub>d (Call ''down'') : stf(Call ''down'', T\<^sub>d)"
  apply (simp add: T\<^sub>d_def)
  apply jc_auto+
  apply (rule_tac \<phi>' = "stf(SKIP;;SKIP, T\<^sub>d)" in CONS, simp)
  apply jc_auto
  apply tfi_auto
  apply (rule_tac \<phi>' = "stf(SKIP, T\<^sub>d) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>d)
     \<Zcat> stf(Call ''down'', fmap_of_list [(''down'', IF Eq (Var ''x'') (Num 0)
        THEN SKIP ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;(Call ''down'') FI)])" in CONS, simp)
  apply auto
  apply jc_auto
  apply (simp add: sequent_valid_def)
  by tfi_auto

end