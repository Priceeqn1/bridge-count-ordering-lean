import CommonTime.Subsets
import CommonTime.Targets

/-!
# Theorem 4.7(a) and the `θ ≥ 1` case of (b)

For the Toeplitz kernel `K(n, j) = b_{n-j}` of display (28) (`stepKernel`),
`K` is TP₂ iff `θ ≥ 1`, and in that case the existing prefix/suffix count-array
theorems apply.
-/

namespace CommonTime

variable {k : ℕ}

theorem stepKernel_fullTP2 {θ : ℝ} (hθ : 1 ≤ θ) : FullTP2 (stepKernel k θ) := by
  intro u v i j huv hij
  simp only [stepKernel]
  simp only [Fin.lt_def] at huv hij ⊢
  have hθ0 : 0 ≤ θ := by linarith
  split_ifs <;> first | (exfalso; omega) | nlinarith

theorem stepKernel_positiveColumnTP2 {θ : ℝ} (hθ : 1 ≤ θ) :
    PositiveColumnTP2 (stepKernel k θ) :=
  fun u v i j huv hij _ => stepKernel_fullTP2 hθ u v i j huv hij

/-- For `k ≥ 4` and `θ < 1` the kernel is not TP₂ (rows 3, 4, columns 1, 2). -/
theorem stepKernel_not_positiveColumnTP2 {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1) (hk : 4 ≤ k) :
    ¬ PositiveColumnTP2 (stepKernel k θ) := by
  intro h
  have := h ⟨3, by omega⟩ ⟨4, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) (by simp)
  simp only [stepKernel, Fin.lt_def] at this
  norm_num at this
  nlinarith

theorem stepKernel_not_fullTP2 {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1) (hk : 4 ≤ k) :
    ¬ FullTP2 (stepKernel k θ) :=
  fun h => stepKernel_not_positiveColumnTP2 hθ0 hθ hk
    (fun u v i j huv hij _ => h u v i j huv hij)

/-- **Theorem 4.7(a).** For `k ≥ 4` and `θ > 0`: `K` is TP₂ iff `θ ≥ 1`. -/
theorem theorem_4_7_a {θ : ℝ} (hθ0 : 0 < θ) (hk : 4 ≤ k) :
    FullTP2 (stepKernel k θ) ↔ 1 ≤ θ := by
  constructor
  · intro h
    by_contra hc
    exact stepKernel_not_fullTP2 hθ0 (not_le.mp hc) hk h
  · exact stepKernel_fullTP2

theorem theorem_4_7_a' {θ : ℝ} (hθ0 : 0 < θ) (hk : 4 ≤ k) :
    PositiveColumnTP2 (stepKernel k θ) ↔ 1 ≤ θ := by
  constructor
  · intro h
    by_contra hc
    exact stepKernel_not_positiveColumnTP2 hθ0 (not_le.mp hc) hk h
  · exact stepKernel_positiveColumnTP2

/-- `θ ≥ 1` case of Theorem 4.7(b), prefix clause. -/
theorem toeplitz_prefix_count_array_TP2_ge_one {θ : ℝ} (hθ : 1 ≤ θ) {k q : ℕ}
    (hq0 : 1 ≤ q) (hqk : q < k) (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg (minor (prefixArray k q r s (stepKernel k θ))
      (prefixArray k q r s' (stepKernel k θ))
      (prefixArray k q r' s (stepKernel k θ)) (prefixArray k q r' s' (stepKernel k θ))) :=
  prefix_count_array_TP2 k q (stepKernel k θ) (stepKernel_tri θ)
    (stepKernel_pos (by linarith)) (stepKernel_positiveColumnTP2 hθ) hq0 hqk r r' s s' hr hs

/-- `θ ≥ 1` case of Theorem 4.7(b), suffix clause. -/
theorem toeplitz_suffix_count_array_TP2_ge_one {θ : ℝ} (hθ : 1 ≤ θ) {k q : ℕ}
    (hq0 : 1 ≤ q) (hqk : q < k) (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg (minor (suffixArray k q r s (stepKernel k θ))
      (suffixArray k q r s' (stepKernel k θ))
      (suffixArray k q r' s (stepKernel k θ)) (suffixArray k q r' s' (stepKernel k θ))) :=
  suffix_count_array_TP2 k q (stepKernel k θ) (stepKernel_tri θ)
    (stepKernel_pos (by linarith)) (stepKernel_fullTP2 hθ) hq0 hqk r r' s s' hr hs

end CommonTime
