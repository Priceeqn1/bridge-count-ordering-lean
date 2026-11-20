# Theorem 4.7 — completed Lean integration and certificate

**Status (20 November 2026): merged and kernel-checked.** [PR #1](https://github.com/Priceeqn1/bridge-count-ordering-lean/pull/1) was merged into `main` on 20 November 2026 (00:36 EST). This file preserves the source inventory, verification evidence, and scope of the completed manuscript-fidelity review.

- **Verified source commit:** `a2f19a951087c827b0967eadfc18772d0c2b455c` (head of PR #1).
- **Merge commit on `main`:** `f52e1cfc0454bdfe421995da6aa803fd65e6b85f`.
- **Source integrity:** The merge commit has the **same Git tree SHA** as the verified PR commit, `6552f243a51c9ab3910feab14a8e9426b73428fd`. No proof source changed during merging.
- **Passing build and axiom audit:** [GitHub Actions run 44678555412](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/44678555412). The build reported `Build completed successfully (9068 jobs)`, and the last `#print axioms` reported `'CommonTime.theorem_4_7' depends on axioms: [propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**.
- **Successful post-merge `main` verification:** [Actions run 44682196989](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/44682196989) passed the complete Lean build (9068 jobs), the focused axiom audits, and the proof-gap check. The final theorem again depended only on `[propext, Classical.choice, Quot.sound]`.
- **Fidelity audit:** [Review recorded on PR #1](https://github.com/Priceeqn1/bridge-count-ordering-lean/pull/1#issuecomment-7031387629). The final theorem statement was compared with Section 4.3 / Theorem 4.7 of the 17 November 2026 AAM manuscript v1.6 and no material statement mismatch was found.

## Source provenance

The twelve Theorem 4.7 source modules came from the supplied `bcol_theorem47_files.zip` (19–20 November 2026). Its SHA-256 manifest was checked. Five previously supplied conversation source files agreed with their archived counterparts except for trailing final newline.

## Source modules and mathematical roles

- `CommonTime/Subsets.lean` — admissible paths ↔ vertex sets and prefix-array representation
- `CommonTime/Chain.lean` — abstract coupled-chain lemma and cut inequality
- `CommonTime/ChainEnum.lean` — chain subset enumeration and recursion
- `CommonTime/Bonds.lean` — bond factorization and chain-pair sums
- `CommonTime/Normalize.lean` — exact path-weight normalization
- `CommonTime/Grouping.lean` — multiplicity fibres and prefix core inequality
- `CommonTime/Coefficient.lean` — coefficientwise prefix theorem
- `CommonTime/SuffixCore.lean` — suffix count and swapped-chain inequality
- `CommonTime/SuffixCoeff.lean` — coefficientwise suffix theorem
- `CommonTime/Witness.lean` — explicit sharpness witness
- `CommonTime/ToeplitzTP2.lean` — kernel TP₂ iff `θ ≥ 1` and high-`θ` case
- `CommonTime/Theorem47.lean` — combined sharp iff characterizations

`CommonTime.lean` imports all twelve modules, so `lake build` checks them as part of the library build.

## Exact theorem scope

For the Toeplitz jump weights `b₀=0`, `b₁=1`, `b_d=θ` for `d≥2` and `θ>0`:

1. **Theorem 4.7(a):** kernel full TP₂ on every finite endpoint truncation `k≥4` holds exactly for `θ≥1` (`CommonTime.theorem_4_7_a`).
2. **Theorem 4.7(b):** all prefix/suffix count-array minors, with `1≤q<k`, `r<r'`, `s<s'`, are coefficientwise nonnegative for all endpoints exactly for `θ≥1/2` (`CommonTime.theorem_4_7_b`).
3. **Sharpness:** at `k=5` and `q=1`, the coefficient of `a₁a₃a₄` in the specified minor is `θ²(2θ−1)` (`CommonTime.witness_coeff`), negative for `0<θ<1/2`.

The combined theorem is `CommonTime.theorem_4_7`.

The reviewed statement agrees with the manuscript as to parameter domain, cuts, count conventions, determinant orientation, independent activity coefficients, and sharp threshold. The Lean derivation uses a generalized binary-chain recursion and a direct swapped-chain suffix proof, whereas the manuscript describes some steps using run/convolution lemmas and reflection. **This certification does not claim** that every standalone intermediate manuscript lemma or the classical log-concavity equivalence has been separately formalized, nor that all results in the paper are Lean-checked.

## Reproduce the kernel and proof-gap checks

```bash
lake build
lake env lean ProofAuditTheorem47Chain.lean
lake env lean ProofAuditTheorem47ChainEnum.lean
lake env lean ProofAuditTheorem47Bonds.lean
lake env lean ProofAuditTheorem47Normalize.lean
lake env lean ProofAuditTheorem47Prefix.lean
lake env lean ProofAuditTheorem47Suffix.lean
lake env lean ProofAuditTheorem47.lean
python3 scripts/check_no_gaps.py
```

GitHub Actions runs these commands alongside the original six-theorem audits. Expected foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`. There must be no `sorryAx` or other unexpected assumption.

## Editorial note

The formal-verification remark, AI-use note, and version-specific repository reference in the manuscript needed updating from the six-target baseline to the verified Theorem 4.7 revision. An updated Overleaf package was prepared separately for author review. This repository documentation records the certification without asserting that such manuscript edits have been incorporated into a submitted or published version.
