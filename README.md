# Bridge-count ordering in Lean 4 — partial formal certification

Lean 4 formalization companion to Hardisty, *Jump-count ordering beyond total positivity in weighted increasing paths* (AAM working draft v1.5, 14 November 2026).

**Status (15 November 2026): FOUR OF SIX TARGETS CERTIFIED; TWO STILL OPEN.** Lean 4 / mathlib 4.35.0 has kernel-checked both backward time–state minor theorems, the crossing-time minor theorem, and the principal prefix count-array theorem. Each completed target's `#print axioms` output contains only `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**. The two remaining targets for suffix-count arrays and jump-count log-concavity still have explicit `sorry` placeholders. **The full two-sided manuscript theorem is NOT yet Lean-certified; the prefix half is.**

**Verification evidence:**
- [Successful backward-minor build and axiom audit](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43677296331)
- [Successful crossing-time build and axiom audit](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43677795777)
- [Successful prefix-count theorem build and axiom audit](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43678802965)
- `ProofAuditBackward.lean`, `ProofAuditCrossing.lean`, and `ProofAuditPrefix.lean` are independently runnable audit entrypoints.
- GitHub Actions' **Build the Lean project** job passes for the proven lemmas; its separate **Reject proof gaps and unapproved axioms** job intentionally fails because two remaining targets are unfinished. A project-wide green certificate does not yet exist.

## Scope of the formalization

- `MvPolynomial (Fin (k+1)) ℝ` represents the independent activity variables and exact coefficientwise positivity, not numerical substitution.
- Paths are finite strictly increasing vertex sequences, starting at 0 and ending at an arbitrary finite endpoint.
- Full and positive-column TP₂ hypotheses are separate. The prefix theorem puts no TP₂ restriction on column zero.
- The kernel-checked crossing-time lemma holds also for the boundary cut `q = 0`; it needs only `q < z.val` and has no `q ≥ 1` hypothesis. For the manuscript's internal cuts `1 ≤ q < k`, this is the same result with a slightly stronger Lean statement.
- All completed results quantify over arbitrary finite endpoints rather than testing a fixed `k`.

## Main project files

- `CommonTime/Definitions.lean`: path, activity polynomial, kernel and count-array definitions
- `CommonTime/Algebra.lean`: elementary Cauchy–Binet algebra
- `CommonTime/BackwardMinor.lean`: complete generalized backward time/state minor proof
- `CommonTime/Crossing.lean`: complete crossing-time minor proof, last-jump recursions, and coefficientwise transport lemma
- `CommonTime/Prefix.lean`: complete common-time splitting proof of the principal prefix-count TP₂ theorem
- `CommonTime/Targets.lean`: the six precise theorem targets (four proved, two open)
- `ProofAuditBackward.lean`, `ProofAuditCrossing.lean`, `ProofAuditPrefix.lean`: axiom reports for the certified theorems
- `scripts/independent_poly_checks.py`: exact finite-endpoint checks (supporting evidence, not a proof)

## Reproduce

Install Lean 4 via `elan` (<https://lean-lang.org/install/manual/>), then run:

```bash
lake update
lake exe cache get
lake build
lake env lean ProofAuditBackward.lean
lake env lean ProofAuditCrossing.lean
lake env lean ProofAuditPrefix.lean
python3 scripts/independent_poly_checks.py
python3 scripts/check_no_gaps.py  # EXPECTED TO FAIL until all remaining targets are proved
```

When all six targets are completed, run `lake env lean ProofAudit.lean` and confirm the absence of `sorryAx`, `admit`, unproved custom axioms, and weakened hypotheses. A formal certificate proves the *formal statement*; the equivalence with the manuscript's theorems must also be reviewed independently.

The work derives from AI-assisted mathematical exploration. Lean's ordinary kernel, not an AI model's assertion, is the authority for the four currently certified targets.
