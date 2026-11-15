# Bridge-count ordering in Lean 4 — partial formal certification

Lean 4 formalization companion to Hardisty, *Jump-count ordering beyond total positivity in weighted increasing paths* (AAM working draft v1.5, 14 November 2026).

**Status (15 November 2026): THREE OF SIX TARGETS CERTIFIED; THREE STILL OPEN.** Lean 4 / mathlib 4.35.0 has kernel-checked both backward time–state minor theorems and the crossing-time minor theorem. Each completed target's `#print axioms` output contains only `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**. The three remaining targets for prefix-count arrays, suffix-count arrays, and jump-count log-concavity still have explicit `sorry` placeholders. **The manuscript's main count-array theorem is NOT yet Lean-certified.**

**Verification evidence:**
- [Successful backward-minor build and axiom audit](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43677296331)
- [Successful crossing-time build and axiom audit](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43677795777)
- `ProofAuditBackward.lean` and `ProofAuditCrossing.lean` are independently runnable audit entrypoints.
- GitHub Actions' **Build the Lean project** job passes for the proven lemmas; its separate **Reject proof gaps and unapproved axioms** job intentionally fails because the three main targets remain unfinished. A project-wide green certificate does not yet exist.

## Scope of the formalization

- `MvPolynomial (Fin (k+1)) ℝ` represents the independent activity variables and exact coefficientwise positivity, not numerical substitution.
- Paths are finite strictly increasing vertex sequences, starting at 0 and ending at an arbitrary finite endpoint.
- Full and positive-column TP₂ hypotheses are separate. The prefix theorem puts no TP₂ restriction on column zero.
- All completed results quantify over arbitrary finite endpoints rather than testing a fixed `k`.

## Main project files

- `CommonTime/Definitions.lean`: path, activity polynomial, kernel and count-array definitions
- `CommonTime/Algebra.lean`: elementary Cauchy–Binet algebra
- `CommonTime/BackwardMinor.lean`: complete generalized backward time/state minor proof
- `CommonTime/Crossing.lean`: complete crossing-time minor proof, last-jump recursions, and coefficientwise transport lemma
- `CommonTime/Targets.lean`: the six precise theorem targets (three proved, three open)
- `ProofAuditBackward.lean`, `ProofAuditCrossing.lean`: axiom reports for the certified theorems
- `scripts/independent_poly_checks.py`: exact finite-endpoint checks (supporting evidence, not a proof)

## Reproduce

Install Lean 4 via `elan` (<https://lean-lang.org/install/manual/>), then run:

```bash
lake update
lake exe cache get
lake build
lake env lean ProofAuditBackward.lean
lake env lean ProofAuditCrossing.lean
python3 scripts/independent_poly_checks.py
python3 scripts/check_no_gaps.py  # EXPECTED TO FAIL until all remaining targets are proved
```

When all six targets are completed, run `lake env lean ProofAudit.lean` and confirm the absence of `sorryAx`, `admit`, unproved custom axioms, and weakened hypotheses. A formal certificate proves the *formal statement*; the equivalence with the manuscript's theorems must also be reviewed independently.

The work derives from AI-assisted mathematical exploration. Lean's ordinary kernel, not an AI model's assertion, is the authority for the three currently certified targets.
