import CommonTime

/-!
  Kernel dependency audit. Run with:
      lake env lean ProofAudit.lean

  Both backward minor theorems are proved (no `sorryAx`); the
  four remaining targets are unfinished and still involve `sorryAx`.
  Once proved, the expected remaining axioms are the Lean/mathlib foundations
  (typically `propext`, `Classical.choice`, and `Quot.sound`).
-/

#print axioms CommonTime.cauchy_binet_two_terms
#print axioms CommonTime.backward_time_state_minor_positive
#print axioms CommonTime.backward_time_state_minor_full
#print axioms CommonTime.crossing_time_minor
#print axioms CommonTime.prefix_count_array_TP2
#print axioms CommonTime.suffix_count_array_TP2
#print axioms CommonTime.jump_count_logconcavity
