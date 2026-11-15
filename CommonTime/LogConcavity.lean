import CommonTime.Prefix

/-!
# Coefficientwise log-concavity of the jump-count weights (Corollary 3.11)

`jumpCountWeight k m K` is the total weight `C_m` of `m`-jump increasing paths
`0 → k`. This file proves

  `C_a * C_b - C_c * C_d ⪰ 0` coefficientwise,
  whenever `c ≤ a ≤ b ≤ d` and `a + b = c + d`,

under strict lower-triangularity, positivity on admissible edges and full TP2.

Structure:
1. path sums are matrix-power entries: `G^m(y) = (T^m)(y,0)`
   (`forwardWeight_eq_pow`), hence `C_m = h_m(0)`
   (`jumpCountWeight_eq_backwardWeight`);
2. one-step inequality `C_{t+1} C_{t'} - C_t C_{t'+1} ⪰ 0` for `t < t'`, from
   the full-TP2 backward time/state lemma at columns `0 < w`;
3. telescoping over the shift `j = a - c`.

Full TP2 is needed here because column `0` of the kernel enters.
Nothing here evaluates the activities at numbers and nothing bounds `k`.
-/

namespace CommonTime

variable {k : ℕ}

/-! ## 1. Path sums are matrix-power entries -/

/-- The only `0`-jump path is the constant path at `0`:
    `G^0(y) = 1` if `y = 0` and `0` otherwise. -/
theorem forwardWeight_zero (K : Vertex k → Vertex k → ℝ) (y : Vertex k) :
    forwardWeight k 0 K y
      = (1 : Matrix (Vertex k) (Vertex k) (Poly k)) y ⟨0, Nat.zero_lt_succ k⟩ := by
  classical
  unfold forwardWeight pathsTo
  rw [Finset.sum_filter]
  have hW : ∀ p : Path k 0, pathWeight k 0 K p = 1 := by
    intro p
    unfold pathWeight
    exact Fin.prod_univ_zero _
  by_cases hy : y = ⟨0, Nat.zero_lt_succ k⟩
  · rw [hy, Matrix.one_apply_eq,
      Fintype.sum_eq_single (fun _ => (⟨0, Nat.zero_lt_succ k⟩ : Vertex k))]
    · rw [ite_eq_left (show admissibleTo k 0 ⟨0, Nat.zero_lt_succ k⟩
        (fun _ => (⟨0, Nat.zero_lt_succ k⟩ : Vertex k)) from
          ⟨rfl, rfl, fun i => absurd i.isLt (Nat.not_lt_zero _)⟩)]
      exact hW _
    · intro p hp
      apply ite_eq_right
      intro hadm
      apply hp
      funext i
      have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by have := i.isLt; omega)
      rw [hi]
      exact hadm.1
  · rw [Matrix.one_apply_ne hy]
    apply Finset.sum_eq_zero
    intro p _
    apply ite_eq_right
    intro hadm
    exact hy (hadm.2.1.symm.trans hadm.1)

/-- `G^m(y) = (T^m)(y,0)`: the sum over explicit `m`-jump increasing paths
    `0 → y` is a matrix-power entry. -/
theorem forwardWeight_eq_pow {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (m : ℕ) :
    ∀ y : Vertex k,
      forwardWeight k m K y
        = ((transitionMatrix k K) ^ m) y ⟨0, Nat.zero_lt_succ k⟩ := by
  induction m with
  | zero =>
    intro y
    rw [pow_zero]
    exact forwardWeight_zero K y
  | succ m ih =>
    intro y
    rw [forwardWeight_succ htri, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro w _
    have hT : transitionMatrix k K y w = stepWeight K y w := rfl
    rw [ih w, hT, mul_comm]

/-- `C_m = h_m(0)`. -/
theorem jumpCountWeight_eq_backwardWeight {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (m : ℕ) :
    jumpCountWeight k m K = backwardWeight k m K ⟨0, Nat.zero_lt_succ k⟩ := by
  have h : jumpCountWeight k m K = forwardWeight k m K ⟨k, Nat.lt_succ_self k⟩ := rfl
  rw [h, forwardWeight_eq_pow htri m]
  rfl

/-! ## 2. One-step inequality -/

/-- `h_{t+1}(0) * h_{t'}(0) - h_t(0) * h_{t'+1}(0) ⪰ 0` for `t < t'`. -/
theorem backward_zero_step {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : FullTP2 K) (t t' : ℕ) (ht : t < t') :
    CoeffNonneg
      (backwardWeight k (t + 1) K ⟨0, Nat.zero_lt_succ k⟩
          * backwardWeight k t' K ⟨0, Nat.zero_lt_succ k⟩
        - backwardWeight k t K ⟨0, Nat.zero_lt_succ k⟩
          * backwardWeight k (t' + 1) K ⟨0, Nat.zero_lt_succ k⟩) := by
  rw [backwardWeight_succ K t, backwardWeight_succ K t', Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply coeffNonneg_sum
  intro w _
  by_cases hw : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) < w
  · have hH := backward_minor_aux_full htri hpos hK t t' ht ⟨0, Nat.zero_lt_succ k⟩ w hw
    have e :
        backwardWeight k t K w * transitionMatrix k K w ⟨0, Nat.zero_lt_succ k⟩
            * backwardWeight k t' K ⟨0, Nat.zero_lt_succ k⟩
          - backwardWeight k t K ⟨0, Nat.zero_lt_succ k⟩
            * (backwardWeight k t' K w * transitionMatrix k K w ⟨0, Nat.zero_lt_succ k⟩)
        = (backwardWeight k t K w * backwardWeight k t' K ⟨0, Nat.zero_lt_succ k⟩
            - backwardWeight k t K ⟨0, Nat.zero_lt_succ k⟩ * backwardWeight k t' K w)
          * transitionMatrix k K w ⟨0, Nat.zero_lt_succ k⟩ := by
      ring
    rw [e]
    exact coeffNonneg_mul hH (coeffNonneg_transitionMatrix htri hpos w _)
  · rw [transitionMatrix_eq_zero htri (le_of_not_gt hw), mul_zero, zero_mul, mul_zero,
      mul_zero, sub_zero]
    exact coeffNonneg_zero

/-! ## 3. Telescoping -/

/-- `h_a(0) * h_b(0) - h_{a-j}(0) * h_{b+j}(0) ⪰ 0` for `j ≤ a ≤ b`. -/
theorem backward_zero_logconcave {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : FullTP2 K) (j : ℕ) :
    ∀ a b : ℕ, j ≤ a → a ≤ b →
      CoeffNonneg
        (backwardWeight k a K ⟨0, Nat.zero_lt_succ k⟩
            * backwardWeight k b K ⟨0, Nat.zero_lt_succ k⟩
          - backwardWeight k (a - j) K ⟨0, Nat.zero_lt_succ k⟩
            * backwardWeight k (b + j) K ⟨0, Nat.zero_lt_succ k⟩) := by
  induction j with
  | zero =>
    intro a b _ _
    have e1 : a - 0 = a := Nat.sub_zero a
    have e2 : b + 0 = b := Nat.add_zero b
    rw [e1, e2, sub_self]
    exact coeffNonneg_zero
  | succ j ih =>
    intro a b hja hab
    have h1 := ih a b (by omega) hab
    have h2 := backward_zero_step htri hpos hK (a - (j + 1)) (b + j) (by omega)
    have e1 : a - (j + 1) + 1 = a - j := by omega
    rw [e1] at h2
    have h3 := coeffNonneg_add h1 h2
    have e :
        backwardWeight k a K ⟨0, Nat.zero_lt_succ k⟩
            * backwardWeight k b K ⟨0, Nat.zero_lt_succ k⟩
          - backwardWeight k (a - (j + 1)) K ⟨0, Nat.zero_lt_succ k⟩
            * backwardWeight k (b + j + 1) K ⟨0, Nat.zero_lt_succ k⟩
        = (backwardWeight k a K ⟨0, Nat.zero_lt_succ k⟩
              * backwardWeight k b K ⟨0, Nat.zero_lt_succ k⟩
            - backwardWeight k (a - j) K ⟨0, Nat.zero_lt_succ k⟩
              * backwardWeight k (b + j) K ⟨0, Nat.zero_lt_succ k⟩)
          + (backwardWeight k (a - j) K ⟨0, Nat.zero_lt_succ k⟩
              * backwardWeight k (b + j) K ⟨0, Nat.zero_lt_succ k⟩
            - backwardWeight k (a - (j + 1)) K ⟨0, Nat.zero_lt_succ k⟩
              * backwardWeight k (b + j + 1) K ⟨0, Nat.zero_lt_succ k⟩) := by
      ring
    show CoeffNonneg
      (backwardWeight k a K ⟨0, Nat.zero_lt_succ k⟩
          * backwardWeight k b K ⟨0, Nat.zero_lt_succ k⟩
        - backwardWeight k (a - (j + 1)) K ⟨0, Nat.zero_lt_succ k⟩
          * backwardWeight k (b + j + 1) K ⟨0, Nat.zero_lt_succ k⟩)
    rw [e]
    exact h3

/-- Manuscript Corollary 3.11 in the form used by the target. -/
theorem jump_count_logconcavity_aux {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : FullTP2 K) (a b c d : ℕ)
    (hca : c ≤ a) (hab : a ≤ b) (hsum : a + b = c + d) :
    CoeffNonneg (jumpCountWeight k a K * jumpCountWeight k b K -
      jumpCountWeight k c K * jumpCountWeight k d K) := by
  rw [jumpCountWeight_eq_backwardWeight htri a, jumpCountWeight_eq_backwardWeight htri b,
    jumpCountWeight_eq_backwardWeight htri c, jumpCountWeight_eq_backwardWeight htri d]
  have h := backward_zero_logconcave htri hpos hK (a - c) a b (by omega) hab
  have e1 : a - (a - c) = c := by omega
  have e2 : b + (a - c) = d := by omega
  rw [e1, e2] at h
  exact h

end CommonTime
