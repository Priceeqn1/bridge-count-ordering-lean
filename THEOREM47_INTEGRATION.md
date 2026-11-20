# Theorem 4.7 — Lean integration checkpoint

**Branch:** `theorem47-integration-20261119` (draft PR #1; `main` unchanged).

## Source provenance and status

All twelve source modules of the new Theorem 4.7 development are now staged on this branch, from Fable's supplied `bcol_theorem47_files.zip` (2026-11-19/20). The archive's `SHA256SUMS.txt` manifest was checked against its contents. Five modules previously staged from conversation uploads matched the ZIP sources modulo trailing final newline.

**This is NOT YET a kernel certificate.** A successful current-commit `lake build`, focused `#print axioms` audits, and manuscript/Lean fidelity review are required before merging or updating the paper's formal-verification remark.

## New Lean modules

- `CommonTime/Subsets.lean` — paths ↔ vertex sets and prefix-array representation
- `CommonTime/Chain.lean` — abstract coupled-chain lemma and cut inequality
- `CommonTime/ChainEnum.lean` — chain subset enumeration and recursion
- `CommonTime/Bonds.lean` — bond factorization and chain-pair sums
- `CommonTime/Normalize.lean` — normalization of path weights
- `CommonTime/Grouping.lean` — multiplicity fibres and prefix core inequality
- `CommonTime/Coefficient.lean` — coefficientwise prefix theorem
- `CommonTime/SuffixCore.lean` — suffix chain and combinatorial inequality
- `CommonTime/SuffixCoeff.lean` — coefficientwise suffix theorem
- `CommonTime/Witness.lean` — explicit necessity witness
- `CommonTime/ToeplitzTP2.lean` — TP₂ iff θ ≥ 1 and high-θ case
- `CommonTime/Theorem47.lean` — the sharp combined theorem

`CommonTime.lean` imports all twelve, so `lake build` cannot silently skip their typechecking.

## Reproduce

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

The CI workflow now runs these checks along with the six original audits. Final `CommonTime.theorem_4_7` must exclude `sorryAx`; ordinary `propext`, `Classical.choice` and `Quot.sound` are expected Lean foundations.

## Statement-faithfulness review

Confirm all endpoints, prefix/suffix cut conventions and indices; arbitrary activities and all ordered minors; the finite `k ≥ 4` restriction on kernel TP₂ sharpness; the coefficient of `a₁ a₃ a₄` at `k=5`; and the `θ > 0` / `θ ≥ 1/2` thresholds. Do not merge until CI is green and this comparison has been completed.
