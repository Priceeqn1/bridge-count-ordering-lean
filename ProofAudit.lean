import CommonTime

/-!
  Kernel dependency audit. Run with:
      lake env lean ProofAudit.lean

  All six theorem targets are Lean kernel-checked. A completed project-wide
  CI run confirms the absence of `sorryAx` in all six reports.
  Their dependencies are the standard Lean/mathlib foundations:
  `propext`, `Classical.choice`, and `Quot.sound`.
-/

#print axioms CommonTime.cauchy_binet_two_terms
#print axioms CommonTime.backward_time_state_minor_positive
#print axioms CommonTime.backward_time_state_minor_full
#print axioms CommonTime.crossing_time_minor
#print axioms CommonTime.prefix_count_array_TP2
#print axioms CommonTime.suffix_count_array_TP2
#print axioms CommonTime.jump_count_logconcavity
