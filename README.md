# Bridge-count ordering in Lean 4 — partial formal certification

Goal: a Lean-checked proof of the new common-time theorem in Hardisty, *Jump-count ordering beyond total positivity in weighted increasing paths*, AAM working draft v1.5 (14 November 2026).

**Current status (15 November 2026): TWO THEOREMS CERTIFIED, FOUR TARGETS OPEN.** Both backward time–state minor theorems, `CommonTime.backward_time_state_minor_positive` and `CommonTime.backward_time_state_minor_full`, have complete Lean 4 proofs via the Fable-derived generalized induction in `CommonTime/BackwardMinor.lean`. The pinned mathlib build passed, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for this theorem, with **no `sorryAx`**. See [successful build and axiom audit](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43677296331). Four further theorems remain `sorry`; the **main count-array theorem is not yet certified**. The project-wide proof-gap job intentionally remains red until those four obligations are proved.

## Why this encoding

- `MvPolynomial (Fin (k+1)) ℝ` enforces independent activities and exact coefficientwise positivity, so numeric substitution cannot accidentally prove a weaker theorem.
- Paths are all functions on finite vertex times filtered by strict monotonicity. They begin at 0 and end at k.
- Full and positive-column TP₂ hypotheses are **separate**. The prefix theorem has no restriction on column-zero minors.
- Results are quantified for all finite endpoints k and all pairs of ordered count indices.

## Use (macOS/Linux, requires internet on initial setup)

1. Install Lean 4 through `elan`: https://lean-lang.org/install/manual/ .
2. Unpack and open this folder in VS Code with Lean 4 extension.
3. Run `lake update && lake exe cache get && lake build`.
4. Run `python3 scripts/check_no_gaps.py` (EXPECTED TO FAIL until targets are proved).
5. Run `lake env lean ProofAuditBackward.lean` to reproduce the certified lemma audit. After all targets are proved, run `lake env lean ProofAudit.lean` to print every theorem’s axiom dependencies. Confirm absence of `sorryAx` and unexpected axioms.
6. Compare theorem signatures against `FORMALIZATION_MAP.md` and the manuscript. A Lean certificate only proves exactly what Lean has been asked to prove.

For an intermediate check independent of Lean: `python3 scripts/independent_poly_checks.py`. This tests a finite set of kernels by exact monomial coefficient arithmetic; it is NOT a substitute for formal verification.

**Axiom AXLE** may be used to check and debug Lean declarations, but hosted AXLE is not the open-source kernel itself. The final reproducible proof should compile under ordinary Lean 4/mathlib at the pinned version.

## Proven versus outstanding

- Proposed algebraic core: `CommonTime/Algebra.lean` (`ring` proof; not typechecked here).
- Formal path and count array specification: `CommonTime/Definitions.lean` (not typechecked here).
- **Proved:** both positive-column and full-column backward time–state minors: `CommonTime/BackwardMinor.lean` and `CommonTime/Targets.lean` (no `sorry` in this theorem; axiom-audited).
- **Still open:** crossing-time minor, prefix-count theorem, suffix-count theorem, and log-concavity: `CommonTime/Targets.lean` (four explicit `sorry` placeholders).
- The two h variants and E lemma are explicit targets; proof bodies remain open.

GitHub Actions has a passing **Lean build + focused backward-minor axiom audit**, but a failing **whole-project completion** job because four other proofs are unfinished. This is intentional; a green build alone does not certify all manuscript claims.
