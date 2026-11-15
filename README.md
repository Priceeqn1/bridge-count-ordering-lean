# Bridge-count ordering in Lean 4 — formalization project (NOT YET CERTIFIED)

Goal: a Lean-checked proof of the new common-time theorem in Hardisty, *Jump-count ordering beyond total positivity in weighted increasing paths*, AAM working draft v1.5 (14 November 2026).

**Current status:** specification + proof-target scaffold; the elementary two-term algebraic identity is written with `ring`; six lemma/theorem targets are explicitly marked `sorry`. **No Lean certificate exists yet.** The current working environment has no `lean`/`lake` binary and cannot reach external installers; thus even the syntax has not been compiled here. Do not cite this project as a completed Lean formalization in the paper.

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
5. After all targets are proved, run `lake env lean ProofAudit.lean` to print every theorem’s axiom dependencies. Confirm absence of `sorryAx` and unexpected axioms.
6. Compare theorem signatures against `FORMALIZATION_MAP.md` and the manuscript. A Lean certificate only proves exactly what Lean has been asked to prove.

For an intermediate check independent of Lean: `python3 scripts/independent_poly_checks.py`. This tests a finite set of kernels by exact monomial coefficient arithmetic; it is NOT a substitute for formal verification.

**Axiom AXLE** may be used to check and debug Lean declarations, but hosted AXLE is not the open-source kernel itself. The final reproducible proof should compile under ordinary Lean 4/mathlib at the pinned version.

## Proven versus outstanding

- Proposed algebraic core: `CommonTime/Algebra.lean` (`ring` proof; not typechecked here).
- Formal path and count array specification: `CommonTime/Definitions.lean` (not typechecked here).
- Two signed common-time lemmas plus core prefix theorem, suffix theorem, log-concavity: `CommonTime/Targets.lean` (explicit `sorry`, **unproved**).
- The two h variants and E lemma are explicit targets; proof bodies remain open.

GitHub Actions workflow reports incomplete certificates as failures intentionally. No false-green certification.