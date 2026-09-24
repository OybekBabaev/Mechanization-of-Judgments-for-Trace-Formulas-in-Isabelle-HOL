theory "Easy_Examples"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

(* x := 3 ; y := 7 *)

lemma "\<Gamma> \<turnstile>\<^sub>T (''x'' := Num 3;;SKIP;;''y'' := Num 7)
          : Rel (Sb ''x'' (Num 3)) \<Zcat> Rel Id \<Zcat> Rel (Sb ''y'' (Num 7))"
  apply seq
  apply assign
  apply seq
  apply skip
  by assign

(* x := 2 ; x := 4 ; x := 3 *)

lemma "\<Gamma> \<turnstile>\<^sub>T (''x'' := Num 2;;''x'' := Num 4;;''x'' := Num 3)
      : Rel (Sb ''x'' (Num 2)) \<Zcat> Rel (Sb ''x'' (Num 4)) \<Zcat> Rel (Sb ''x'' (Num 3))"
  apply seq
  apply assign
  apply seq
  apply assign
  by assign

(* if True then x := 4 ; y := 4 else skip *)

lemma "\<Gamma> \<turnstile>\<^sub>T (IF TRUE THEN (''x'' := Num 4);;(''y'' := Num 4) ELSE SKIP FI)
        : stf(IF TRUE THEN (''x'' := Num 4);;(''y'' := Num 4) ELSE SKIP FI, T)"
  apply ite
  apply (cons "stf (SKIP;;(''x'' := Num 4);;(''y'' := Num 4), T)")
  apply seq
  apply skip
  apply seq
  apply assign
  apply assign
  defer
  apply (cons "stf (SKIP;;SKIP, T)")
  apply seq
  apply skip
  apply skip
  by tfi_auto

(* with proof automation *)

lemma "\<Gamma> \<turnstile>\<^sub>T (''x'' := Num 3;;SKIP;;''y'' := Num 7)
          : Rel (Sb ''x'' (Num 3)) \<Zcat> Rel Id \<Zcat> Rel (Sb ''y'' (Num 7))"
  by jc_auto

lemma "\<Gamma> \<turnstile>\<^sub>T (''x'' := Num 2;;''x'' := Num 4;;''x'' := Num 3)
      : Rel (Sb ''x'' (Num 2)) \<Zcat> Rel (Sb ''x'' (Num 4)) \<Zcat> Rel (Sb ''x'' (Num 3))"
  by jc_auto

lemma "\<Gamma> \<turnstile>\<^sub>T (IF TRUE THEN (''x'' := Num 4);;(''y'' := Num 4) ELSE SKIP FI)
        : stf(IF TRUE THEN (''x'' := Num 4);;(''y'' := Num 4) ELSE SKIP FI, T)"
  apply jc_auto
  apply (cons "stf (SKIP;;(''x'' := Num 4);;(''y'' := Num 4), T)")
  apply jc_auto
  defer
  apply (cons "stf (SKIP;;SKIP, T)")
  apply jc_auto
  by tfi_auto

end