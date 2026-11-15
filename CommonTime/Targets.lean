import CommonTime.Definitions
import CommonTime.Algebra

/-!
# Formalization targets for Version 1.5

IMPORTANT: the `sorry` placeholders below mark UNPROVED targets.
This is a mathematically faithful statement scaffold, NOT a certificate.
The repository's `certificate` CI job intentionally rejects these.

Target order:
1. coefficientwise Cauchy--Binet and elementary closure lemmas;
2. backward time/state minor lemma h;
3. crossing-time minor lemma E;
4. prefix joint-array theorem for positive-column TP2;
5. suffix joint-array theorem under full TP2;
6. jump-count log-concavity.

See FORMALIZATION_MAP.md for the exact corresponding paper equations.
-/

namespace CommonTime

/-- Manuscript Lemma 3.8: reverse-sign backward time/state minors.
    Positive-column hypothesis is valid only for 1 ≤ z < z'. -/
theorem backward_time_state_minor_positive
    (k : ℕ) (K : Vertex k → Vertex k → ℝ)
    (htri : StrictLowerTriangular K)
    (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K)
    (z z' : Vertex k) (hz0 : 0 < z.val) (hzz' : z < z')
    (t t' : ℕ) (htt' : t < t') :
    CoeffNonneg
      (backwardWeight k t K z' * backwardWeight k t' K z -
       backwardWeight k t K z * backwardWeight k t' K z') := by
  sorry

/-- Manuscript Lemma 3.8 under full TP2, now also permitting z=0. -/
theorem backward_time_state_minor_full
    (k : ℕ) (K : Vertex k → Vertex k → ℝ)
    (htri : StrictLowerTriangular K)
    (hpos : PositiveAdmissible K)
    (hK : FullTP2 K)
    (z z' : Vertex k) (hzz' : z < z')
    (t t' : ℕ) (htt' : t < t') :
    CoeffNonneg
      (backwardWeight k t K z' * backwardWeight k t' K z -
       backwardWeight k t K z * backwardWeight k t' K z') := by
  sorry

/-- Manuscript Lemma 3.9: reverse-sign first-crossing minors.
    This is the E^theta_rho polynomial statement; not a numeric test. -/
theorem crossing_time_minor
    (k theta q rho rho' : ℕ) (K : Vertex k → Vertex k → ℝ)
    (htri : StrictLowerTriangular K)
    (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K)
    (hq0 : 1 ≤ q)
    (hrr' : rho < rho') (hr't : rho' < theta)
    (z z' : Vertex k) (hqz : q < z.val) (hzz' : z < z') :
    CoeffNonneg
      (crossingWeight k theta q rho K z' * crossingWeight k theta q rho' K z -
       crossingWeight k theta q rho K z * crossingWeight k theta q rho' K z') := by
  sorry

/-- Full prefix count-array property (the stronger part of Theorem 3.10).
    The column-zero entries of `K` are only assumed positive on their
    admissible edges. -/
theorem prefix_count_array_TP2
    (k q : ℕ) (K : Vertex k → Vertex k → ℝ)
    (htri : StrictLowerTriangular K)
    (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K)
    (hq0 : 1 ≤ q) (hqk : q < k)
    (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg (minor
      (prefixArray k q r s K) (prefixArray k q r s' K)
      (prefixArray k q r' s K) (prefixArray k q r' s' K)) := by
  sorry

/-- Two-sided theorem: suffix arrays under full kernel TP2. -/
theorem suffix_count_array_TP2
    (k q : ℕ) (K : Vertex k → Vertex k → ℝ)
    (htri : StrictLowerTriangular K)
    (hpos : PositiveAdmissible K)
    (hK : FullTP2 K)
    (hq0 : 1 ≤ q) (hqk : q < k)
    (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg (minor
      (suffixArray k q r s K) (suffixArray k q r s' K)
      (suffixArray k q r' s K) (suffixArray k q r' s' K)) := by
  sorry

/-- Coefficientwise log-concavity of the jump-count weights. -/
theorem jump_count_logconcavity
    (k : ℕ) (K : Vertex k → Vertex k → ℝ)
    (htri : StrictLowerTriangular K)
    (hpos : PositiveAdmissible K)
    (hK : FullTP2 K)
    (a b c d : ℕ)
    (hchain : 1 ≤ c ∧ c ≤ a ∧ a ≤ b ∧ b ≤ d ∧ d ≤ k)
    (hsum : a + b = c + d) :
    CoeffNonneg (jumpCountWeight k a K * jumpCountWeight k b K -
      jumpCountWeight k c K * jumpCountWeight k d K) := by
  sorry

end CommonTime
