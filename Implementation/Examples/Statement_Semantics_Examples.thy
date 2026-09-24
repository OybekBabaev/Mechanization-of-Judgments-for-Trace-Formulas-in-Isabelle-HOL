theory Statement_Semantics_Examples
  imports "../Rec_Semantics"
begin

type_synonym Tmap = "(method_name, S) fmap"

(* examples for Rec semantics *)

definition s\<^sub>0 :: state where "s\<^sub>0 \<equiv> fmap_of_list [(''x'', 0), (''y'', 0)]"

lemma "(fmempty, [fmempty]) \<in> rec_sem (SKIP, fmempty) \<I>"
  by (simp add: rec_sem_def)

lemma "(s\<^sub>0, [fmempty]) \<notin> rec_sem (SKIP, fmempty) \<I>"
  by (simp add: rec_sem_def s\<^sub>0_def)

lemma "(s\<^sub>0, [s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>\<langle>''y'' \<longmapsto> 2\<rangle>])
         \<in> rec_sem ((''x'' := Num 2);;(''y'' := Num 2), fmempty) \<I>"
  by (simp add: rec_sem_def)

lemma "(s\<^sub>0, [s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>])
    \<notin> rec_sem ((''x'' := Num 2);;(''x'' := Num 4);;(''x'' := Num 3),
                fmempty) \<I>"
  by (simp add: rec_sem_def)

lemma "(s\<^sub>0, [s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>\<langle>''y'' \<longmapsto> 3\<rangle>])
         \<in> rec_sem ((''x'' := Num 3);;SKIP;;(''y'' := Num 3), fmempty) \<I>"
  by (simp add: rec_sem_def)

lemma "(s\<^sub>0, [s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>\<langle>''y'' \<longmapsto> 3\<rangle>])
         \<notin> rec_sem ((''x'' := Num 3);;SKIP;;(''y'' := Num 3), fmempty) \<I>"
  by (simp add: rec_sem_def)

lemma "(s\<^sub>0, [s\<^sub>0, s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>\<langle>''y'' \<longmapsto> 4\<rangle>])
    \<in> rec_sem (IF TRUE THEN (''x'' := Num 4);;(''y'' := Num 4) ELSE SKIP FI, fmempty) \<I>"
  by (simp add: rec_sem_def)

lemma "(s\<^sub>0, [s\<^sub>0, s\<^sub>0\<langle>''x'' \<longmapsto> 5\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 5\<rangle>\<langle>''y'' \<longmapsto> 5\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 5\<rangle>\<langle>''y'' \<longmapsto> 5\<rangle>\<langle>''z'' \<longmapsto> 1\<rangle>])
    \<in> rec_sem (IF (Not (Eq (Var ''x'') (Var ''y''))) THEN SKIP
        ELSE ((''x'' := Num 5);;(''y'' := Num 5);;(''z'' := Num 1)) FI,
      fmempty) \<I>"
  by (simp add: rec_sem_def s\<^sub>0_def)

definition T\<^sub>6 :: Tmap where
  "T\<^sub>6 = fmap_of_list [(''foo'', (''x'' := Num 6);;(''y'' := ((Var ''x'') \<oplus> (Var ''y'')))),
            (''bar'', (''x'' := ((Var ''x'') \<oplus> (Var ''y'')));;(''y'' := Num 0))]"

lemma "(s\<^sub>0, [s\<^sub>0, s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>\<langle>''y'' \<longmapsto> 6\<rangle>])
        \<in> rec_sem (Call ''foo'', T\<^sub>6) \<I>"
  apply (simp add: rec_sem_def initial_interpretation_def T\<^sub>6_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  by (simp add: sem_ops_def s\<^sub>0_def)

lemma "(s\<^sub>0, [s\<^sub>0, s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>\<langle>''y'' \<longmapsto> 6\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>\<langle>''y'' \<longmapsto> 6\<rangle>, s\<^sub>0\<langle>''y'' \<longmapsto> 6\<rangle>\<langle>''x'' \<longmapsto> 12\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 12\<rangle>\<langle>''y'' \<longmapsto> 0\<rangle>])
    \<in> rec_sem ((Call ''foo'');;(Call ''bar''), T\<^sub>6) \<I>"
  apply (simp add: rec_sem_def initial_interpretation_def T\<^sub>6_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def)
  apply (rule exI[of _ "[s\<^sub>0, s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>]"])
  apply (rule exI[of _ "s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>\<langle>''y'' \<longmapsto> 6\<rangle>"])
  apply (rule exI[of _ "[s\<^sub>0\<langle>''x'' \<longmapsto> 6\<rangle>\<langle>''y'' \<longmapsto> 6\<rangle>, s\<^sub>0\<langle>''y'' \<longmapsto> 6\<rangle>\<langle>''x'' \<longmapsto> 12\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 12\<rangle>\<langle>''y'' \<longmapsto> 0\<rangle>]"])
  apply simp
  apply (intro conjI)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def s\<^sub>0_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def s\<^sub>0_def)
  by (auto simp add: fmap_ext)

definition T\<^sub>7 :: Tmap where
  "T\<^sub>7 = fmap_of_list [(''even'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 1)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''odd'') FI)),
        (''odd'', (IF Eq (Var ''x'') (Num 0)
          THEN (''y'' := Num 0)
          ELSE (''x'' := ((Var ''x'' \<ominus> (Num 1))));;(Call ''even'') FI))]"

lemma "(s\<^sub>0, [s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 1\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 1\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 1\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 0\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 0\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 0\<rangle>,
      s\<^sub>0\<langle>''y'' \<longmapsto> 1\<rangle>])
     \<in> rec_sem ((''x'' := Num 4);;(Call ''even''), T\<^sub>7) \<I>"
  apply (auto simp add: rec_sem_def initial_interpretation_def T\<^sub>7_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def)
  apply (subst lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def)
  by (auto simp add: fmap_ext s\<^sub>0_def)

lemma "(s\<^sub>0, [s\<^sub>0\<langle>''x'' \<longmapsto> 4\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 3\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 2\<rangle>,
      s\<^sub>0\<langle>''x'' \<longmapsto> 1\<rangle>, s\<^sub>0\<langle>''x'' \<longmapsto> 0\<rangle>, s\<^sub>0\<langle>''y'' \<longmapsto> 1\<rangle>])
     \<notin> rec_sem ((''x'' := Num 4);;(Call ''even''), T\<^sub>7) \<I>"
  apply (auto simp add: rec_sem_def initial_interpretation_def T\<^sub>7_def)
  apply (subst (asm) lfp_unfold[OF sem_ops_mono])
  apply (simp add: sem_ops_def s\<^sub>0_def)
  apply (auto simp add: fmap_ext)
  apply (drule arg_cong[where f="\<lambda>m. fmlookup m ''x''"])
  by simp

end