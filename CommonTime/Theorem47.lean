import CommonTime.Witness
import CommonTime.SuffixCoeff
import CommonTime.ToeplitzTP2

/-!
# Theorem 4.7 (Toeplitz count-array TP₂ without log-concavity)

`K(n, j) = b_{n-j}`, `b₀ = 0`, `b₁ = 1`, `b_d = θ` for `d ≥ 2` (`stepKernel`).

* (a) `K` is TP₂ iff `θ ≥ 1` (`theorem_4_7_a`, for `k ≥ 4`).
* (b) The universal coefficientwise count-MLR inequality, for every endpoint and
  every prefix/suffix interval, holds iff `θ ≥ 1/2` (`theorem_4_7_b`).
-/

namespace CommonTime

/-- Necessity witness: `k = 5`, `q = 1`, `r = 1`, `r' = 2`, `s = 0`, `s' = 1`. -/
theorem prefix_witness_fails {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ¬ CoeffNonneg (minor (prefixArray 5 1 1 0 (stepKernel 5 θ))
      (prefixArray 5 1 1 1 (stepKernel 5 θ))
      (prefixArray 5 1 2 0 (stepKernel 5 θ)) (prefixArray 5 1 2 1 (stepKernel 5 θ))) := by
  intro h
  have h1 := h eW
  rw [witness_coeff hθ0.ne'] at h1
  nlinarith [mul_pos hθ0 hθ0]

/-- **Theorem 4.7(b).** For `θ > 0`, the count-array minors of the Toeplitz kernel are
    coefficientwise nonnegative for every endpoint `k` and every prefix/suffix
    interval `[1, q]` / `[q, k-1]` (`1 ≤ q < k`) iff `θ ≥ 1/2`. -/
theorem theorem_4_7_b {θ : ℝ} (hθ0 : 0 < θ) :
    (∀ (k q r r' s s' : ℕ), 1 ≤ q → q < k → r < r' → s < s' →
      CoeffNonneg (minor (prefixArray k q r s (stepKernel k θ))
        (prefixArray k q r s' (stepKernel k θ))
        (prefixArray k q r' s (stepKernel k θ)) (prefixArray k q r' s' (stepKernel k θ)))
      ∧ CoeffNonneg (minor (suffixArray k q r s (stepKernel k θ))
        (suffixArray k q r s' (stepKernel k θ))
        (suffixArray k q r' s (stepKernel k θ)) (suffixArray k q r' s' (stepKernel k θ))))
    ↔ 1 / 2 ≤ θ := by
  constructor
  · intro h
    by_contra hc
    exact prefix_witness_fails hθ0 (not_le.mp hc)
      (h 5 1 1 2 0 1 le_rfl (by norm_num) (by norm_num) (by norm_num)).1
  · intro hθ k q r r' s s' hq hqk hr hs
    rcases le_total θ 1 with h1 | h1
    · exact ⟨toeplitz_prefix_count_array_TP2 hθ h1 hq hqk r r' s s' hr hs,
        toeplitz_suffix_count_array_TP2 hθ h1 (by omega) r r' s s' hr hs⟩
    · exact ⟨toeplitz_prefix_count_array_TP2_ge_one h1 hq hqk r r' s s' hr hs,
        toeplitz_suffix_count_array_TP2_ge_one h1 hq hqk r r' s s' hr hs⟩

/-- **Theorem 4.7**, parts (a) and (b), for `θ > 0`. -/
theorem theorem_4_7 {θ : ℝ} (hθ0 : 0 < θ) :
    (∀ k : ℕ, 4 ≤ k → (FullTP2 (stepKernel k θ) ↔ 1 ≤ θ))
    ∧ ((∀ (k q r r' s s' : ℕ), 1 ≤ q → q < k → r < r' → s < s' →
      CoeffNonneg (minor (prefixArray k q r s (stepKernel k θ))
        (prefixArray k q r s' (stepKernel k θ))
        (prefixArray k q r' s (stepKernel k θ)) (prefixArray k q r' s' (stepKernel k θ)))
      ∧ CoeffNonneg (minor (suffixArray k q r s (stepKernel k θ))
        (suffixArray k q r s' (stepKernel k θ))
        (suffixArray k q r' s (stepKernel k θ)) (suffixArray k q r' s' (stepKernel k θ))))
    ↔ 1 / 2 ≤ θ) :=
  ⟨fun _ hk => theorem_4_7_a hθ0 hk, theorem_4_7_b hθ0⟩

end CommonTime
