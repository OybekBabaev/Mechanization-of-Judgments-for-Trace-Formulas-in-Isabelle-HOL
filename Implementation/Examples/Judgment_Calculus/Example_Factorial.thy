theory "Example_Factorial"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

type_synonym Tmap = "(method_name, S) fmap"

(* fact(), which is *)
(* if n \<le> 1 then skip else x := xn ; n := n - 1 ; fact() *)

definition T\<^sub>f :: Tmap where
  "T\<^sub>f = fmap_of_list [(''fact'', IF Leq (Var ''n'') (Num 1)
      THEN SKIP
      ELSE ''x'' := (Var ''x'' \<otimes> Var ''n'');;
        ''n'' := (Var ''n'' \<ominus> Num 1);;Call ''fact'' FI)]"

lemma "[] \<turnstile>\<^sub>T\<^sub>f (Call ''fact'') : stf(Call ''fact'', T\<^sub>f)"
  apply (simp add: T\<^sub>f_def)
  apply call
  apply unfold
  apply ite
  apply (rule_tac \<phi>' = "stf(SKIP;;SKIP, T\<^sub>f)" in CONS, simp)
  apply (seq, skip, skip)
  apply tfi_auto
  apply (rule_tac \<phi>' = "stf(SKIP, T\<^sub>f) \<Zcat> stf(''x'' := Var ''x'' \<otimes> Var ''n'', T\<^sub>f)
    \<Zcat> stf(''n'' := Var ''n'' \<ominus> Num 1, T\<^sub>f)
    \<Zcat> stf(Call ''fact'', fmap_of_list [(''fact'', IF Leq (Var ''n'') (Num 1)
      THEN SKIP ELSE ''x'' := (Var ''x'' \<otimes> Var ''n'');;
        ''n'' := (Var ''n'' \<ominus> Num 1);;Call ''fact'' FI)])" in CONS, simp)
  apply auto
  apply (seq, skip)
  apply (seq, assign)
  apply (seq, assign)
  apply (seq, skip)
  apply (simp add: sequent_valid_def)
  by tfi_auto

(* the same, but with new proof automation *)

lemma "[] \<turnstile>\<^sub>T\<^sub>f (Call ''fact'') : stf(Call ''fact'', T\<^sub>f)"
  apply (simp add: T\<^sub>f_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;SKIP, T\<^sub>f)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>f) \<Zcat> stf(''x'' := Var ''x'' \<otimes> Var ''n'', T\<^sub>f)
    \<Zcat> stf(''n'' := Var ''n'' \<ominus> Num 1, T\<^sub>f)
    \<Zcat> stf(Call ''fact'', fmap_of_list [(''fact'', IF Leq (Var ''n'') (Num 1)
      THEN SKIP ELSE ''x'' := (Var ''x'' \<otimes> Var ''n'');;
        ''n'' := (Var ''n'' \<ominus> Num 1);;Call ''fact'' FI)])")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  by tfi_auto

end