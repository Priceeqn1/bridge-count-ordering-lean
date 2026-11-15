# Mathematical statement map — AAM Version 1.5

This file is intended for a specialist who will independently compare the Lean statements with the human-readable paper. **A passing Lean build is not enough** without confirming the theorem statement is the same as in print.

## Manuscript version and exact targets

Source: `Jump_Count_Ordering_AAM_v1_5_Overleaf.zip`, `main.tex`, Section 3, the subsection **From prefix tails to full count arrays**. We use the source as reference only; no edits to the manuscript are made here.

| Source concept | Lean declaration | Fidelity notes |
|---|---|---|
| States \(0,\ldots,k\) | `Vertex k := Fin (k+1)` | All finite endpoints, not a fixed tested size |
| Admissible increasing path | `admissible k m p` | Starts at 0, ends at k, every step strictly increases |
| Independent activities \(a_1,\ldots,a_{k-1}\), with \(a_0=1\) | `activity` and `stepWeight` | `X₀` and `X_k` may exist in ambient polynomial algebra but never occur in a positive-length admissible path |
| Full kernel TP₂ | `FullTP2 K` | Every ordered minor, including column 0 |
| Positive-column TP₂ | `PositiveColumnTP2 K` | No determinant hypothesis involving column 0; positive admissible edge weights remain assumed |
| Coefficientwise nonnegative polynomial | `CoeffNonneg p` | For **all** monomials, real coefficient ≥ 0 |
| Prefix count array \(H^{[1,q]}_{r,s}\) | `prefixArray k q r s K` | `r` intermediate vertices; `r+1` jumps |
| Suffix count array \(H^{[q,k-1]}_{r,s}\) | `suffixArray k q r s K` | Same route weight and row index |
| Theorem 3.10, positive-column prefix extension | `prefix_count_array_TP2` | Full array, NOT just tails |
| Theorem 3.10, two-sided full-TP₂ clause | `suffix_count_array_TP2` | Uses full TP₂, not positive columns |
| Corollary 3.11 log-concavity | `jump_count_logconcavity` | Coefficientwise, arbitrary k, a+b=c+d |

**Kernel certification complete (15 November 2026):** all six formal targets and their supporting lemmas compiled under the pinned Lean 4/mathlib environment. The repository-wide proof-gap check passed, and `ProofAudit.lean` reported only `propext`, `Classical.choice`, and `Quot.sound` for every target. [Successful certification run](https://github.com/Priceeqn1/bridge-count-ordering-lean/actions/runs/43680554382). Independent comparison of these exact statements with the manuscript remains an outstanding scholarly audit.

## Realized formal proof architecture

1. Establish `CoeffNonneg` closure under finite sums, products, and the coefficient convolution of `MvPolynomial`.
2. Establish finite 2x2 Cauchy–Binet for polynomial-valued matrices.
3. Define strictly lower triangular matrix powers `T^m` and prove they agree with `pathWeight` sums.
4. Define `h_t(z)` and `E^theta_rho(z)` with exact crossing-time semantics.
5. Prove their ordered minors coefficientwise nonpositive, with the positive-column restriction for z,z'≥1.
6. Split all four path sums at a common jump index to prove every prefix count-array minor nonnegative.
7. Prove suffix minors directly from full kernel TP₂, using forward-weight minors, suffix-core/suffix-tail decomposition, and a common-time split counted backward from the path endpoint (no state-space reflection).
8. Derive jump-count log-concavity via the time/state lemma.

## Issues to check while formalizing

- The base t=0 case of the backward minor lemma and finite zero-support terms.
- The base theta=2 case of the crossing lemma, especially column-zero avoidance.
- The case q=k-1, empty/degenerate arrays, and infeasible numbers of visits.
- The precise orientation of determinant signs, including reflected paths.
- The difference between k=0,1 vacuous statements and k≥2 with genuine cuts.
- The coefficientwise claims over **arbitrary real positive** K values, not just integer-valued test kernels.
