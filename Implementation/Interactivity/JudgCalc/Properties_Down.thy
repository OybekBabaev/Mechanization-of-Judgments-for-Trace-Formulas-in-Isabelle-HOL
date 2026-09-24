theory "Properties_Down"
  imports "../../TFI_Prover" "../../JC_Prover"
begin

definition R_x_dec :: "(state \<times> state) set" where
  [rels]: "R_x_dec \<equiv> {(s, s'). s\<langle>''x''\<rangle> \<ge> s'\<langle>''x''\<rangle>}"

type_synonym Tmap = "(method_name, S) fmap"

(* down(), which is *)
(* if x == 0 then skip else x := x - 1 ; down() *)

definition T\<^sub>d :: Tmap where
  "T\<^sub>d = fmap_of_list [(''down'', IF Eq (Var ''x'') (Num 0)
        THEN SKIP ELSE ''x'' := (Var ''x'' \<ominus> Num 1);;Call ''down'' FI)]"

(* example 1 *)
(* Variable x never increases throughout execution - PROVEN *)
lemma "[] \<turnstile>\<^sub>T\<^sub>d (Call ''down'') : (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))"
  apply (rule_tac \<phi>' = "(Rel Id) \<Zcat> (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))" in CONS)
  defer
  apply tfi_auto
  apply (rule CALL)
  apply (simp add: T\<^sub>d_def)+
  apply unfold
  apply jc_auto
  apply (cons "stf(SKIP;;SKIP, T\<^sub>d)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>d) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>d)
    \<Zcat> stf(SKIP, T\<^sub>d) \<Zcat> (\<mu> ''dec''. (Rel R_x_dec \<squnion> Rel R_x_dec \<Zcat> RVar ''dec''))")
  apply jc_auto
  apply (simp_all add: sequent_valid_def)
  by tfi_auto

(* example 2 *)
(* If variable x not negative to begin with, then call terminates - PROVEN 1 *)
lemma "[] \<turnstile>\<^sub>T\<^sub>d (Call ''down'') : (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0))"
  apply (rule_tac \<phi>' = "(Rel Id) \<Zcat> (Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0))" in CONS)
  defer
  apply tfi_auto
  apply (rule CALL)
  apply (simp_all add: T\<^sub>d_def)+
  apply jc_auto
  apply (cons "stf(SKIP;;SKIP, T\<^sub>d)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>d) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>d)
    \<Zcat> stf(SKIP, T\<^sub>d) \<Zcat> (Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0))")
  apply seq
  apply skip
  apply seq
  apply assign
  apply seq
  apply skip
  apply (simp_all add: sequent_valid_def)
  by tfi_auto

(* example 2 *)
(* If variable x not negative to begin with, then call terminates - ABANDONED 2 *)
lemma "[] \<turnstile>\<^sub>T\<^sub>d (Call ''down'') : (Rel Id \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0)))"
  apply (simp add: T\<^sub>d_def)
  apply jc_auto+
  apply (cons "stf(SKIP;;SKIP, T\<^sub>d)")
  apply jc_auto
  apply tfi_auto
  apply (cons "stf(SKIP, T\<^sub>d) \<Zcat> stf(''x'' := (Var ''x'' \<ominus> Num 1), T\<^sub>d)
    \<Zcat> stf(SKIP, T\<^sub>d) \<Zcat> (Pred (\<lambda>s. s\<langle>''x''\<rangle> < 0) \<squnion> Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0))")
  apply jc_auto
  apply (simp add: sequent_valid_def)+
  apply tfi_auto
  defer
  apply close
  apply arb1
  oops

end