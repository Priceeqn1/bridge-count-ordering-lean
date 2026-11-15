# Bridge-count ordering — Lean 4 formal certificate

Formal verification companion to Hardisty, *Jump-count ordering beyond total positivity in weighted increasing paths* (AAM working draft v1.5, 14 November 2026).

**Status (15 November 2026): ALL SIX THEOREM TARGETS KERNEL-CHECKED.** The project's pinned Lean 4 / mathlib v4.35.0 build passed, as did its separate proof-gap and unapproved-axiom detection job. The independent `#print axioms` report for all six targets contains only `[propext, Classical.choice, Quot.sound]` and **no `sorryAx`**.

- [Complete successful GitHub Actions workflow, including all six audits](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43680554382)
- Both backward time–state minor theorems: positive-column TP₂ and full TP₂.
- The crossing-time minor theorem (including boundary cut `q = 0`, with `q < z`).
- The entire coefficientwise TP₂ **prefix-count array** under positive-column kernel TP₂.
- The entire coefficientwise TP₂ **suffix-count array** under full kernel TP₂.
- Coefficientwise jump-count log-concavity under full kernel TP₂.

**Scope caution:** These are formal certificates for the precise statements in `CommonTime/Targets.lean`. An independent theorem-by-theorem **manuscript-to-Lean fidelity audit** is still needed before asserting that every detail of the published manuscript is formally verified.

## Mathematics and representation

- Vertices are `Fin (k+1)`, with arbitrary finite endpoint `k`; admissible paths start at 0 and end at `k`, taking strictly increasing jumps.
- `MvPolynomial (Fin (k+1)) ℝ` encodes independent site activities; `CoeffNonneg` quantifies over every monomial rather than sampling numerical activities.
- `FullTP2` covers all ordered kernel minors, including column 0. `PositiveColumnTP2` omits determinants involving column 0, while retaining positive admissible edge weights.
- The prefix result counts intermediate vertices in `[1,q]`. The suffix result counts intermediate vertices in `[q,k-1]`, including `q`; its crossing argument is at `q-1`.
- The suffix proof uses direct forward weights and suffix-tail transport, not a state-space reflection.

## Files

- `CommonTime/Definitions.lean`: model and polynomial definitions.
- `CommonTime/Algebra.lean`: elementary algebra.
- `CommonTime/BackwardMinor.lean`: backward time–state inequalities.
- `CommonTime/Crossing.lean`: first-crossing minors.
- `CommonTime/Prefix.lean`: common-time prefix count-array proof.
- `CommonTime/LogConcavity.lean`: jump-count log-concavity proof.
- `CommonTime/Suffix.lean`: direct suffix count-array proof.
- `CommonTime/Targets.lean`: six certified theorem declarations.
- `ProofAudit*.lean`: focused and combined kernel-axiom reports.
- `FORMALIZATION_MAP.md`: mathematical statement correspondence and remaining fidelity-review questions.

## Reproduce the certification

Install Lean via `elan` (<https://lean-lang.org/install/manual/>), and then run:

```bash
lake update
lake exe cache get
lake build
lake env lean ProofAuditBackward.lean
lake env lean ProofAuditCrossing.lean
lake env lean ProofAuditPrefix.lean
lake env lean ProofAuditLogConcavity.lean
lake env lean ProofAuditSuffix.lean
lake env lean ProofAudit.lean
python3 scripts/check_no_gaps.py
```

Optional independent finite tests: `python3 scripts/independent_poly_checks.py`. These are not a substitute for the proofs.

The Lean kernel, not an AI model's stated confidence, is the final authority on the six formal declarations. The proof was developed with AI assistance and checked reproducibly under ordinary Lean 4/mathlib.
