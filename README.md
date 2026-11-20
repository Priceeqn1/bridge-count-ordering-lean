# Bridge-count ordering — Lean 4 formal certificates

Formal verification companion to Hardisty, *Jump-count ordering beyond total positivity in weighted increasing paths* (AAM working draft v1.6, 17 November 2026).

**Status (20 November 2026): the original six theorem targets and the sharp Toeplitz Theorem 4.7 are kernel-checked.** The project uses Lean 4 / mathlib v4.35.0. The completed Theorem 4.7 integration passed `lake build`, the focused axiom audits, and the repository's proof-gap check. The final `#print axioms CommonTime.theorem_4_7` output lists only `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**.

- [Merged pull request #1 (Theorem 4.7)](https://github.com/Priceeqn1/bridge-count-ordering-lean/pull/1), merged 20 November 2026 into `main`.
- [Successful Theorem 4.7 build and all focused axiom audits](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/44678555412), run on the exact source tree subsequently merged.
- [Post-merge CI workflow on `main`](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/44682196989).
- [Earlier six-target certification workflow](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43680554382).

## Certified mathematical results

### Original six targets (`CommonTime/Targets.lean`)

- Backward time–state minor theorems under positive-column TP₂ and full TP₂.
- Crossing-time minor theorem, including the boundary cut `q = 0` with `q < z`.
- Coefficientwise TP₂ of prefix-count arrays under positive-column kernel TP₂.
- Coefficientwise TP₂ of suffix-count arrays under full kernel TP₂.
- Coefficientwise jump-count log-concavity under full kernel TP₂.

### Sharp Toeplitz separation theorem (`CommonTime/Theorem47.lean`)

For the step-Toeplitz kernel `b₀ = 0`, `b₁ = 1`, `b_d = θ` for `d ≥ 2`, assuming `θ > 0`:

- **Kernel TP₂ iff `θ ≥ 1`**, for every finite truncation with endpoint `k ≥ 4` (Theorem 4.7(a), `theorem_4_7_a`).
- **Universal coefficientwise prefix- and suffix-count-array TP₂ iff `θ ≥ 1/2`**, simultaneously for every endpoint, every `1 ≤ q < k`, and all ordered row/column pairs `r < r'`, `s < s'` (Theorem 4.7(b), `theorem_4_7_b`).
- The necessity witness is the coefficient of `a₁ a₃ a₄` at `k = 5`, `q = 1`: `θ²(2θ − 1)` (`witness_coeff`).
- The combined result is `CommonTime.theorem_4_7`. In particular, `1/2 ≤ θ < 1` is the strict separation regime.

Theorem 4.7 uses a coupled-binary-chain inequality, exact path-weight normalization, and grouping by activity-monomial multiplicity fibres. The prefix and suffix conclusions are **coefficientwise** rather than tests at particular numerical activities.

## Mathematical representation and scope

- Vertices are `Fin (k+1)`. Admissible paths start at 0, end at `k`, and have strictly increasing jumps. A path with `r` intermediate vertices has `r + 1` jumps.
- `MvPolynomial (Fin (k+1)) ℝ` represents independent interior site activities; `CoeffNonneg` quantifies over every monomial.
- `FullTP2` covers all ordered kernel minors, including column 0. `PositiveColumnTP2` omits those involving column 0.
- Prefix counts use `[1,q]`; suffix counts use `[q,k−1]`, including `q`.
- The original general suffix theorem uses direct forward weights and suffix-tail transport. The new Toeplitz suffix theorem uses a swapped coupled-chain comparison.
- A manuscript-to-Lean statement-fidelity review of Theorem 4.7 was completed on 20 November 2026, with **no material mismatch** in the theorem's hypotheses, index conventions, minors, coefficientwise scope, or sharpness witness. See [the PR fidelity review](https://github.com/Priceeqn1/bridge-count-ordering-lean/pull/1#issuecomment-7031387629).
- **Limits of certification:** The theorem is verified as formally stated in Lean; this does not individually certify every auxiliary run/convolution lemma in the manuscript, the classical Toeplitz/log-concavity equivalence in full generality, or every other result in the AAM draft. Different but equivalent proof strategies are used in parts of the paper and Lean.

## Source modules

The original formalization is in `CommonTime/Definitions.lean`, `Algebra.lean`, `BackwardMinor.lean`, `Crossing.lean`, `Prefix.lean`, `Suffix.lean`, `LogConcavity.lean` and `Targets.lean`.

Theorem 4.7 adds `CommonTime/Subsets.lean`, `Chain.lean`, `ChainEnum.lean`, `Bonds.lean`, `Normalize.lean`, `Grouping.lean`, `Coefficient.lean`, `SuffixCore.lean`, `SuffixCoeff.lean`, `Witness.lean`, `ToeplitzTP2.lean`, and `Theorem47.lean`.

The `ProofAudit*.lean` files implement the axiom checks. [`THEOREM47_INTEGRATION.md`](THEOREM47_INTEGRATION.md) records the integration, provenance, and fidelity review. [`FORMALIZATION_MAP.md`](FORMALIZATION_MAP.md) covers the original targets; historical notes in it should be read in their original revision context.

## Reproduce the certification

Install Lean via [elan](https://lean-lang.org/install/manual/) and run from the repository root:

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
lake env lean ProofAuditTheorem47Chain.lean
lake env lean ProofAuditTheorem47ChainEnum.lean
lake env lean ProofAuditTheorem47Bonds.lean
lake env lean ProofAuditTheorem47Normalize.lean
lake env lean ProofAuditTheorem47Prefix.lean
lake env lean ProofAuditTheorem47Suffix.lean
lake env lean ProofAuditTheorem47.lean
python3 scripts/check_no_gaps.py
```

Optional independent finite tests: `python3 scripts/independent_poly_checks.py`. These supplement but do not replace a Lean proof. The Lean kernel, rather than an AI model's confidence, is the authority on the formal declarations; the formalization was developed with AI assistance and checked under the pinned Lean 4/mathlib toolchain.
