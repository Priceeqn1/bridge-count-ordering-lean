# Theorem 4.7 Lean integration — work in progress

**Branch:** `theorem47-integration-20261119` (staged separately from `main`).

The six earlier Lean theorem targets on `main` are the existing verified baseline.
**Do not describe Theorem 4.7 as kernel-verified yet.** This branch is an integration staging area;
a passed legacy workflow does not by itself certify the new theorem, and missing import files currently
prevent a complete source build.

## Exact Fable sources staged from conversation uploads

- `CommonTime/Subsets.lean` — step kernel, paths ↔ vertex sets, prefix array.
- `CommonTime/ChainEnum.lean` — enumeration ↔ abstract binary-chain recursion.
- `CommonTime/Grouping.lean` — multiplicity fibres, prefix combinatorial core.
- `CommonTime/Coefficient.lean` — polynomial coefficient transfer, prefix top-level theorem.
- `CommonTime/SuffixCore.lean` — suffix counting, swapped chain inequality, suffix core.

These are *source snapshots*, not independently certified Lean modules.

## Remaining dependencies and files

The modules above refer to additional sources not yet committed on this branch:

- `CommonTime/Chain.lean`: the abstract coupled-chain inequalities, including `Zdiff_nonneg`.
- `CommonTime/Bonds.lean`: bond decomposition, `baseCount`, `Zsum`, and `Zsum_eq_Zpair`.
- `CommonTime/Normalize.lean`: `kernelFactor_eq` and `subWeight_pair` (source pasted in chat).
- `CommonTime/SuffixCoeff.lean`: suffix polynomial bridge (source pasted in chat).
- `CommonTime/Witness.lean`: coefficient `θ^2 (2θ-1)` for the sharpness witness (source pasted in chat).
- `CommonTime/ToeplitzTP2.lean`: the `θ≥1` TP₂ regime (source pasted in chat).
- `CommonTime/Theorem47.lean`: assembly of the sharp iff statements (source pasted in chat).

The full `Chain.lean` and `Bonds.lean` files have **not** been provided in the accessible conversation.
Those two files are necessary to complete the import chain.

## Verification order

1. Add the missing sources in their actual `CommonTime/*.lean` paths without modifying `main`.
2. Run `lake env lean CommonTime/Subsets.lean`, then the chain/bond modules, followed by
   `ChainEnum`, `Normalize`, `Grouping`, `Coefficient`, `SuffixCore`,
   `SuffixCoeff`, `Witness`, `ToeplitzTP2`, and `Theorem47`.
3. Run `lake build` and the existing six theorem audits to catch regressions.
4. Run `lake env lean ProofAuditTheorem47.lean` and examine the resulting axiom list;
   in particular, confirm `theorem_4_7` has **no `sorryAx`**.
5. Run `python3 scripts/check_no_gaps.py`.
6. Independently audit the final theorem against the manuscript: all endpoints/cuts/minors;
   independent activity variables; prefix and suffix conventions; `k≥4` for part (a);
   sharpness coefficient for part (b).

Only after those checks pass should the manuscript formal-verification remark be expanded.
