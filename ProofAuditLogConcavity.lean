import CommonTime.Targets

/-! Focused axiom audit for the completed jump-count log-concavity theorem
    (Corollary 3.11).
    Expected to exclude `sorryAx`, while the suffix-array target remains unfinished. -/

#print axioms CommonTime.forwardWeight_eq_pow
#print axioms CommonTime.jumpCountWeight_eq_backwardWeight
#print axioms CommonTime.backward_zero_step
#print axioms CommonTime.jump_count_logconcavity_aux
#print axioms CommonTime.jump_count_logconcavity
