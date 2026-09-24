theory "Properties_Fact"
  imports "../../TFI_Prover"
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

definition Rec_fact :: Rec where
  "Rec_fact \<equiv> (Call ''fact'', T\<^sub>f)"

definition Rec_fact_from_10 :: Rec where
  "Rec_fact_from_10 \<equiv> (''n'' := Num 10;;Call ''fact'', T\<^sub>f)"

definition Rec_fact_from_10_alt :: Rec where
  "Rec_fact_from_10_alt \<equiv> (''n'' := Num 10;;''x'' := Num 0;;Call ''fact'', T\<^sub>f)"

(* example 4 *)
(* Variable x never decreases throughout execution,
   provided x was positive to begin with - PROVEN *)
lemma "[stf Rec_fact] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> \<le> 0) \<squnion> \<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')]"
  apply (simp add: Rec_fact_def T\<^sub>f_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. \<not> s\<langle>''x''\<rangle> \<le> 0")
  apply tfi_auto
  by (simp add: mult_le_0_iff)

(* A slightly modified variant - the predicate comes on the left-hand side *)
lemma "[stf Rec_fact, Pred (\<lambda>s. \<not> s\<langle>''x''\<rangle> \<le> 0)] \<turnstile> [\<mu> ''inc''. (Rel R_x_inc \<squnion> Rel R_x_inc \<Zcat> RVar ''inc'')]"
  apply (simp add: Rec_fact_def T\<^sub>f_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. \<not> s\<langle>''x''\<rangle> \<le> 0")
  apply tfi_auto
  by (simp add: mult_le_0_iff)

(* example 5 *)
(* Variable x never decreases throughout execution
   and variable n stays gte 1,
   provided x was positive to begin with - PROVEN *)
lemma "[stf Rec_fact_from_10] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> \<le> 0) \<squnion> \<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]"
  apply (simp add: Rec_fact_from_10_def T\<^sub>f_def)
  apply tfi_auto
  apply (fpi_alt "\<lambda>s. s\<langle>''n''\<rangle> \<ge> 1 \<and> \<not> s\<langle>''x''\<rangle> \<le> 0")
  apply tfi_auto
  by (simp add: mult_le_0_iff)

(* example 5a *)
(* Same as above, but variable x set to 0 explicitly,
   no predicate given - NOT DERIVABLE (cannot prove that n stays gte 1) *)
lemma "[stf Rec_fact_from_10_alt] \<turnstile> [\<mu> ''combo''. (Rel R_combo \<squnion> Rel R_combo \<Zcat> RVar ''combo'')]"
  apply (simp add: Rec_fact_from_10_alt_def T\<^sub>f_def)
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel (Sb ''x'' (Num 0)) \<Zcat>
     Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''fact''. (Pred (\<lambda>s. s\<langle>''n''\<rangle> \<le> 1) \<sqinter>
                   Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                   Pred (\<lambda>s. \<not> s\<langle>''n''\<rangle> \<le> 1) \<sqinter>
                   Rel Trace_Formulas.Id \<Zcat>
                   Rel (Sb ''x'' (Var ''x'' \<otimes> Var ''n'')) \<Zcat>
                   Rel (Sb ''n'' (Var ''n'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   RVar
                    ''fact'')"
        and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion>
          Rel R_combo \<Zcat> RVar ''combo'')]" in CH_UPD)
  apply simp_all+
  apply rel
  apply unfr
  apply disj_r
  apply (rule_tac \<Phi> = "Rel Trace_Formulas.Id \<Zcat>
     \<mu> ''fact''. (Pred (\<lambda>s. s\<langle>''n''\<rangle> \<le> 1) \<sqinter>
                   Rel Trace_Formulas.Id \<Zcat> Rel Trace_Formulas.Id \<squnion>
                   Pred (\<lambda>s. \<not> s\<langle>''n''\<rangle> \<le> 1) \<sqinter>
                   Rel Trace_Formulas.Id \<Zcat>
                   Rel (Sb ''x'' (Var ''x'' \<otimes> Var ''n'')) \<Zcat>
                   Rel (Sb ''n'' (Var ''n'' \<ominus> Num 1)) \<Zcat>
                   Rel Trace_Formulas.Id \<Zcat>
                   RVar
                    ''fact'')"
        and \<Psi>s = "[\<mu> ''combo''. (Rel R_combo \<squnion>
          Rel R_combo \<Zcat> RVar ''combo'')]" in CH_UPD)
  apply simp_all+
  oops

end