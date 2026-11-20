import CommonTime.SuffixCore
import CommonTime.Coefficient

/-!
# The polynomial bridge for Theorem 4.7(b), suffix clause
-/

open scoped symmDiff

namespace CommonTime

variable {k : ℕ}

theorem minor_expandS (θ : ℝ) (q : ℕ) (r r' s s' : ℕ) :
    minor (suffixArray k q r s (stepKernel k θ)) (suffixArray k q r s' (stepKernel k θ))
      (suffixArray k q r' s (stepKernel k θ)) (suffixArray k q r' s' (stepKernel k θ))
      = ∑ A ∈ vertexSets k (r' + 1), ∑ B ∈ vertexSets k (r + 1),
          ((if suffixCount k q A = s' ∧ suffixCount k q B = s
              then subWeight k θ A * subWeight k θ B else 0)
            - (if suffixCount k q A = s ∧ suffixCount k q B = s'
              then subWeight k θ A * subWeight k θ B else 0)) := by
  unfold minor
  rw [suffixArray_stepKernel θ q r s, suffixArray_stepKernel θ q r s',
    suffixArray_stepKernel θ q r' s, suffixArray_stepKernel θ q r' s',
    sum_mul_sum_swap, sum_mul_sum_swap, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro B _
  rw [ite_mul_ite', ite_mul_ite']

/-- **Suffix clause of Theorem 4.7(b), coefficientwise.** -/
theorem coeff_minor_nonnegS {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 1)
    {q : ℕ} (hk : 1 ≤ k) (r r' s s' : ℕ) (hr : r < r') (hs : s < s')
    (e : Fin (k + 1) →₀ ℕ) :
    0 ≤ (minor (suffixArray k q r s (stepKernel k θ)) (suffixArray k q r s' (stepKernel k θ))
      (suffixArray k q r' s (stepKernel k θ)) (suffixArray k q r' s' (stepKernel k θ))).coeff e := by
  have hψ1 : 1 ≤ θ⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hθ0]
    linarith
  have hψ2 : θ⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hθ0]
    linarith
  rw [minor_expandS θ q r r' s s']
  exact coeff_expanded_nonneg hθ0 hθ1 hθ2 hk (suffixCount k q) (sufN q k)
    (suffixCount_eq_sufN q) r r' s s'
    (fun c => core_nonnegS hψ1 hψ2 k q r r' s s' hr hs c) e

/-- **Theorem 4.7(b), suffix clause, `1/2 ≤ θ ≤ 1`.** -/
theorem toeplitz_suffix_count_array_TP2 {θ : ℝ} (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 1)
    {k q : ℕ} (hk : 1 ≤ k) (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg (minor (suffixArray k q r s (stepKernel k θ))
      (suffixArray k q r s' (stepKernel k θ))
      (suffixArray k q r' s (stepKernel k θ)) (suffixArray k q r' s' (stepKernel k θ))) :=
  fun e => coeff_minor_nonnegS (by linarith) hθ1 hθ2 hk r r' s s' hr hs e

end CommonTime
