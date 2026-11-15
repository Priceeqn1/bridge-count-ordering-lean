# Independent Lean proof task for Claude Fable (High) or another prover

You are formalizing Section 3 of the attached mathematical paper, specifically the newly established common-time decomposition that proves **full coefficientwise TP2 of prefix and suffix joint visit-count arrays** for every finite endpoint. You have been given a Lean 4/mathlib project, `BridgeCountLean`, pinned to Lean/mathlib v4.35.0.

**Do not change the mathematical statements in `CommonTime/Targets.lean` to make them easier.** Do not substitute evaluation at numerical activities, bounded endpoint checks, coefficients over `ℕ` only, or full TP2 for the positive-column prefix hypothesis. Real-valued `K`, arbitrary finite endpoint, coefficientwise polynomial order, and strict increasing paths are essential.

Tasks, in order:

1. Compile `CommonTime/Definitions.lean`; fix only syntactic/typing errors. Confirm `pathWeight`, prefix/suffix visits, and the polynomial coefficient order agree exactly with the paper and `FORMALIZATION_MAP.md`.
2. Prove the algebraic coefficientwise closure lemmas and the general finite 2×2 Cauchy–Binet identity in `MvPolynomial`, checking the signs.
3. Replace the `sorry` in `backward_time_state_minor_positive` with a Lean proof, then prove the full-column version. The base case t=0 and support restrictions are crucial.
4. Prove `crossing_time_minor` by induction in theta, including the case rho'=theta-1, where the input states lie on opposite sides of the spatial cut.
5. Prove `prefix_count_array_TP2` by identifying the common jump index theta=rho'+1 and splitting the four path sums at it. Reflect only for `suffix_count_array_TP2`, under full kernel TP2.
6. Prove `jump_count_logconcavity` with the backward time-state lemma.
7. Run `lake build`, `python3 scripts/check_no_gaps.py`, and `lake env lean ProofAudit.lean`. Record exact commands, output, and all axiom dependencies.

Deliver a source diff and a proof status table. If a target is not proved, say **UNPROVED**, identify the precise remaining Lean goal, and do not insert `axiom`, `opaque`, `native_decide`, `sorry`, `admit`, `unsafe`, or unproved external lemmas to simulate success. If a statement is actually false, produce a concrete finite-dimensional polynomial counterexample and explain the mismatch with the manuscript. If a theorem needs an extra assumption, flag it as a substantive mathematical issue rather than quietly modifying its type.

The final criterion is a complete manuscript-equivalent theorem that the ordinary Lean kernel accepts; the AI model's confidence is irrelevant.
