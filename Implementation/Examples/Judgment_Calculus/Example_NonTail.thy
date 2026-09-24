theory "Example_NonTail"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

type_synonym Tmap = "(method_name, S) fmap"

(* nt(), which is *)
(* if x \<le> 0 then skip else x := x - 1 ; nt() ; y := y + 1 *)

definition T\<^sub>t :: Tmap where
  "T\<^sub>t = fmap_of_list [(''nt'', IF Leq (Var ''x'') (Num 0)
        THEN SKIP
        ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;
              (Call ''nt'');;''y'' := (Var ''y'' \<oplus> Num 1) FI)]"

lemma "[] \<turnstile>\<^sub>T\<^sub>t (Call ''nt'') : stf(Call ''nt'', T\<^sub>t)"
  apply (simp add: T\<^sub>t_def)
  apply call
  apply ite
  apply (cons "stf(SKIP;;SKIP, T\<^sub>t)")
  apply seq
  apply skip
  apply skip
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>t) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>t)
    \<Zcat> stf(Call ''nt'', fmap_of_list [(''nt'', IF Leq (Var ''x'') (Num 0)
        THEN SKIP
        ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;
              (Call ''nt'');;''y'' := (Var ''y'' \<oplus> Num 1) FI)])
    \<Zcat> stf(''y'' := (Var ''y'' \<oplus> Num 1), T\<^sub>t)")
  apply seq
  apply skip
  apply seq
  apply assign
  apply seq
  apply seq
  apply skip
  apply (simp add: sequent_valid_def)
  apply assign
  by tfi_auto

(* the same, but with new proof automation *)

lemma "[] \<turnstile>\<^sub>T\<^sub>t (Call ''nt'') : stf(Call ''nt'', T\<^sub>t)"
  apply (simp add: T\<^sub>t_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;SKIP, T\<^sub>t)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>t) \<Zcat> stf(''x'' := Var ''x'' \<ominus> Num 1, T\<^sub>t)
    \<Zcat> stf(Call ''nt'', fmap_of_list [(''nt'', IF Leq (Var ''x'') (Num 0)
        THEN SKIP
        ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;
              (Call ''nt'');;''y'' := (Var ''y'' \<oplus> Num 1) FI)])
    \<Zcat> stf(''y'' := (Var ''y'' \<oplus> Num 1), T\<^sub>t)")
  apply jc_auto
  apply (simp add: sequent_valid_def)
  apply jc_auto
  by tfi_auto

end