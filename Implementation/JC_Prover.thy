theory JC_Prover
  imports Judgment_Calculus "HOL-Eisbach.Eisbach"
begin

method skip = rule SKIP; fail

method assign = rule ASSIGN; fail

method seq = rule SEQ

method ite = rule IF

method unfold = rule UNFOLD, auto

method call = rule CALL, auto

method cons for phi :: "trace_formula" = (rule CONS[of _ _ _ phi]), simp

method jc_close_proof = (seq | skip | assign)+

method jc_auto = (jc_close_proof | ite | call | unfold)

end