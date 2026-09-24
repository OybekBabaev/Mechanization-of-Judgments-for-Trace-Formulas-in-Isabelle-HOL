theory Trace_Formulas_Examples
  imports "../Trace_Formula_Implication"
begin

notation fmap_of_list ("fm")

definition factorial :: Rec where 
  "factorial \<equiv> (''y'' := Num 1;; Call ''fac'',
   fm [(''fac'', IF Var ''x'' == Num 1 
                 THEN SKIP 
                 ELSE ''y'' := Var ''y'' \<otimes> Var ''x'';;
                      ''x'' := Var ''x'' \<ominus> Num 1;;
                      Call ''fac'' FI)])"

lemma "stf factorial = Rel (Sb ''y'' (Num 1)) \<Zcat>  Rel Id  \<Zcat>
    \<mu> ''fac''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 1) \<sqinter> Rel Id \<Zcat> Rel Id \<squnion>
                Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 1) \<sqinter> Rel Id \<Zcat> Rel (Sb ''y'' (Var ''y'' \<otimes> Var ''x'')) \<Zcat> 
                    Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat> Rel Id \<Zcat> RVar ''fac'')"
  by (auto simp add: factorial_def)

definition even :: Rec where
  "even \<equiv> (Call ''even'',
              (fm [(''even'', IF Var ''x'' == Num 0 THEN ''y'' := Num 1 ELSE ''x'' := Var ''x'' \<ominus> Num 1;; Call ''odd'' FI),
                    (''odd'', IF Var ''x'' == Num 0 THEN ''y'' := Num 0 ELSE ''x'' := Var ''x'' \<ominus> Num 1;; Call ''even'' FI)]))"

lemma "stf even = Rel Id \<Zcat> \<mu> ''even''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter> Rel Id \<Zcat> Rel (Sb ''y'' (Num 1)) \<squnion>
                                        Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter> Rel Id \<Zcat> Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat> Rel Id \<Zcat>
                           \<mu> ''odd''. (Pred (\<lambda>s. s\<langle>''x''\<rangle> = 0) \<sqinter> Rel Id \<Zcat> Rel (Sb ''y'' (Num 0)) \<squnion>
                                       Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 0) \<sqinter> Rel Id \<Zcat> Rel (Sb ''x'' (Var ''x'' \<ominus> Num 1)) \<Zcat> Rel Id \<Zcat> RVar ''even''))"
  by (simp add: even_def)

definition s\<^sub>1 :: state where
  "s\<^sub>1 \<equiv> fm [(''x'', 2), (''y'', 3)]"

lemma "(fmempty, [fmempty]) \<in> \<lbrakk>Rel Id\<rbrakk>\<^sub>\<V>"
  by (simp add: Id_def)

lemma "(s, [s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s, s])
          \<in> \<lbrakk>\<mu> ''x''. (Rel Id \<squnion> Rel Id \<Zcat> RVar ''x'')\<rbrakk>\<^sub>\<V>"
  by (simp add: Id_def subset_iff)

definition inc_traces :: "trace set" where
  "inc_traces \<equiv> semantics (\<mu> ''x''. (Rel (Sb ''x'' (Var ''x'' \<oplus> Num 1)) \<squnion> Rel (Sb ''x'' (Var ''x'' \<oplus> Num 1)) \<Zcat> (RVar ''x''))) fmempty"

lemma abc: "(s\<^sub>1, [s\<^sub>1\<langle>''x'' \<longmapsto> 3\<rangle>]) \<in> inc_traces"
  by (auto simp add: inc_traces_def s\<^sub>1_def Sb_def)

lemma "(s\<langle>''x'' \<longmapsto> 3\<rangle>, [s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  by (auto simp add: inc_traces_def Sb_def)

lemma "(s, [s\<langle>''x'' \<longmapsto> s\<langle>''x''\<rangle> + 1\<rangle>]) \<in> inc_traces"
  by (auto simp add: inc_traces_def Sb_def)

lemma inc_step: "\<lbrakk>s' = s\<langle>''x'' \<longmapsto> s\<langle>''x''\<rangle> + 1\<rangle>; (s', \<sigma>) \<in> inc_traces\<rbrakk> \<Longrightarrow> (s, s' # \<sigma>) \<in> inc_traces"
  by (auto 5 2 simp add: Sb_def inc_traces_def)

lemma inc_end: "\<lbrakk>s' = s\<langle>''x'' \<longmapsto> s\<langle>''x''\<rangle> + 1\<rangle>\<rbrakk> \<Longrightarrow> (s, [s']) \<in> inc_traces"
  by (auto simp add: inc_traces_def Sb_def)

lemma "(s\<langle>''x'' \<longmapsto> 3\<rangle>, [s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  by (auto simp add: inc_traces_def Sb_def)

lemma "(s\<langle>''x'' \<longmapsto> 2\<rangle>, [s\<langle>''x'' \<longmapsto> 3\<rangle>, s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  by (simp | rule inc_end | rule inc_step)+

lemma "(s\<langle>''x'' \<longmapsto> 1\<rangle>, [s\<langle>''x'' \<longmapsto> 2\<rangle>, s\<langle>''x'' \<longmapsto> 3\<rangle>, s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  by (simp | rule inc_end | rule inc_step)+

lemma "(s\<langle>''x'' \<longmapsto> 0\<rangle>, [s\<langle>''x'' \<longmapsto> 1\<rangle>, s\<langle>''x'' \<longmapsto> 2\<rangle>, s\<langle>''x'' \<longmapsto> 3\<rangle>, s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  by (simp | rule inc_end | rule inc_step)+

lemma "(s\<langle>''x'' \<longmapsto> 0\<rangle>, [s\<langle>''x'' \<longmapsto> 1\<rangle>, s\<langle>''x'' \<longmapsto> 2\<rangle>, s\<langle>''x'' \<longmapsto> 3\<rangle>, s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  by (simp | rule inc_end | rule inc_step)+

lemma "(s\<langle>''x'' \<longmapsto> 0\<rangle>, [s\<langle>''x'' \<longmapsto> 1\<rangle>, s\<langle>''x'' \<longmapsto> 2\<rangle>, s\<langle>''x'' \<longmapsto> 3\<rangle>, s\<langle>''x'' \<longmapsto> 4\<rangle>]) \<in> inc_traces"
  apply (rule inc_step)
  apply simp
  apply (rule inc_step)
  apply simp
  apply (rule inc_step)
  apply simp
  apply (rule inc_end)
  by simp

lemma "(s, [s]) \<in> \<lbrakk>Rel Id\<rbrakk>\<^sub>\<V>"
  by (auto simp add: Id_def)

lemma "(s\<^sub>1, [fmempty]) \<notin> \<lbrakk>Rel Id\<rbrakk>\<^sub>\<V>"
  by (auto simp add: s\<^sub>1_def Id_def)

lemma "\<lbrakk>Pred (\<lambda>s. True)\<rbrakk>\<^sub>\<V> = UNIV" by auto

lemma "(fm [(''x'', 3)], [fm [(''x'', 3)], fm [(''x'', 3)], fm [(''x'', 3)]]) \<in> \<lbrakk>Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3)\<rbrakk>\<^sub>\<V>" by auto

lemma "(fm [(''x'', 3)], [fm [(''x'', 3)], fm [(''x'', 3)]]) \<in> \<lbrakk>Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3)\<rbrakk>\<^sub>\<V>" by auto

lemma "(fm [(''x'', 3)], [fm [(''x'', 3)]]) \<in> \<lbrakk>Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3)\<rbrakk>\<^sub>\<V>" by auto

lemma "(fm [(''x'', 3)], []) \<in> \<lbrakk>Pred (\<lambda>s. True) \<Zcat> Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3)\<rbrakk>\<^sub>\<V>" by auto

lemma "(fm [(''x'', 3)], [fm [(''x'', 3)], fm [(''x'', 3)], fm [(''x'', 3)]]) \<in> \<lbrakk>Pred (\<lambda>s. True)\<rbrakk>\<^sub>\<V>" by auto

definition \<Phi>\<^sub>1 :: trace_formula where
  "\<Phi>\<^sub>1 \<equiv> RVar ''1''"

definition \<Phi>\<^sub>2 :: trace_formula where
  "\<Phi>\<^sub>2 \<equiv> RVar ''2''"

definition \<Phi>\<^sub>3 :: trace_formula where
  "\<Phi>\<^sub>3 \<equiv> RVar ''3''"

definition \<V> :: "(string, trace set) fmap" where
  "\<V> \<equiv> fm [(''1'', {(fm [(''x'', 1)], []), (fm [(''x'', 1)], [fm [(''x'', 2)]])}), 
            (''2'', {(fm [(''x'', 1)], [fm [(''x'', 2)]]), (fm [(''x'', 1)], [fm [(''x'', 2)], fm [(''x'', 3)]])}), 
            (''3'', {(fm [(''x'', 1)], [fm [(''x'', 2)], fm [(''x'', 3)], fm [(''x'', 4)]]), (fm [(''x'', 2)], [fm [(''x'', 3)], fm [(''x'', 4)], fm [(''x'', 5)]]), (fm [(''x'', 3)], [fm [(''x'', 4)]])})]"

lemma "(fm [(''x'', 1)], [fm [(''x'', 2)]]) \<in> \<lbrakk>\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2\<rbrakk>\<^sub>\<V>"
  by (auto simp add: \<Phi>\<^sub>1_def \<Phi>\<^sub>2_def \<V>_def)

lemma "(fm [(''x'', 1)], [fm [(''x'', 2)], fm [(''x'', 3)], fm [(''x'', 4)]]) \<notin> \<lbrakk>(\<Phi>\<^sub>1 \<sqinter> \<Phi>\<^sub>2) \<Zcat> \<Phi>\<^sub>3\<rbrakk>\<^sub>\<V>"
  by (auto simp add: \<Phi>\<^sub>1_def \<Phi>\<^sub>2_def \<Phi>\<^sub>3_def \<V>_def) 

lemma 1: "(fm [(''x'', 1)], [fm [(''x'', 2)], fm [(''x'', 3)], fm [(''x'', 4)]]) \<in> \<lbrakk>\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>3\<rbrakk>\<^sub>\<V>"
  by (auto simp add: \<Phi>\<^sub>1_def \<Phi>\<^sub>2_def \<Phi>\<^sub>3_def \<V>_def)

lemma 2: "(fm [(''x'', 1)], [fm [(''x'', 2)], fm [(''x'', 3)], fm [(''x'', 4)]]) \<in> \<lbrakk>\<Phi>\<^sub>2 \<Zcat> \<Phi>\<^sub>3\<rbrakk>\<^sub>\<V>" 
  unfolding \<Phi>\<^sub>1_def \<Phi>\<^sub>2_def \<Phi>\<^sub>3_def \<V>_def 
  apply auto
  by (rule exI [of _ "[fm [(''x'', 2)]]"], auto)

lemma "(fm [(''x'', 1)], [fm [(''x'', 2)], fm [(''x'', 3)], fm [(''x'', 4)]]) \<in> \<lbrakk>\<Phi>\<^sub>1 \<Zcat> \<Phi>\<^sub>3 \<sqinter> \<Phi>\<^sub>2 \<Zcat> \<Phi>\<^sub>3\<rbrakk>\<^sub>\<V>"
  apply (simp add: \<Phi>\<^sub>1_def \<Phi>\<^sub>2_def \<Phi>\<^sub>3_def \<V>_def)
  by (rule exI [of _ "[fm [(''x'', 2)]]"], auto)

lemma "\<xi> \<diamondop> [x, y, z, Pred (\<lambda>s. False), a, b, c] \<turnstile> [d, e, f, g, h]"
  by (rule FALSE, simp)

lemma "\<xi> \<diamondop> [x, y, z, Pred (\<lambda>s. False), a, b, c] \<turnstile> [d, e, f, g, h]"
  by ((rule TRUE, simp; fail) | (rule FALSE, simp; fail) | (rule CLOSE, simp; fail))

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [d, e, Pred (\<lambda>s. True), f, g, h]"
  by (rule TRUE, simp)

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [d, e, Pred (\<lambda>s. True), f, g, h]"
  by ((rule TRUE, simp; fail) | (rule FALSE, simp; fail) | (rule CLOSE, simp; fail))

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [d, e, f, a, g, h, i]"
  by (rule CLOSE, simp)

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [d, e, f, a, g, h, i]"
  by ((rule TRUE, simp; fail) | (rule FALSE, simp; fail) | (rule CLOSE, simp; fail))

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3), Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq>  3)]"
  apply(rule CASE[of _ "(\<lambda>s. s\<langle>''x''\<rangle> = 3)"])
  apply(rule CLOSE, simp)
  by(rule CLOSE, simp)

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3), Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 3)]"
  apply(rule CASE)
  apply(rule CLOSE, auto)
  by(rule CLOSE, auto)

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 3), Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3)]"
  apply(rule CASE)
  apply(rule CLOSE, auto)
  by(rule CLOSE, auto)

lemma "\<xi> \<diamondop> [x, y, z, a, b, c] \<turnstile> [Pred (\<lambda>s. s\<langle>''x''\<rangle> \<noteq> 3), Pred (\<lambda>s. s\<langle>''x''\<rangle> = 3)]"
  apply(rule CASE)
  by ((rule TRUE, simp; fail) | (rule FALSE, simp; fail) | (rule CLOSE, auto))+

lemma "[Pred (\<lambda>s. s\<langle>''x''\<rangle> > 1), Pred (\<lambda>s. s\<langle>''y''\<rangle> \<ge> 1), Rel (Sb ''y'' (Var ''y'' \<otimes> Var ''x''))] \<turnstile> [Rel {(s, s'). s\<langle>''y''\<rangle> \<le> s'\<langle>''y''\<rangle>}]"
  by (rule REL, auto simp add: Sb_def)

end