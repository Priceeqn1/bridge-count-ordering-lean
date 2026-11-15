import CommonTime.Definitions

/-!
# Backward time/state minors (manuscript Lemma 3.8, positive-column form)

This file proves the reverse-sign minor inequality for the backward
polynomials `h_t(z) = (T^t)(k,z)`:

  `h_t(z') * h_{t'}(z) - h_t(z) * h_{t'}(z') ⪰ 0` coefficientwise,
  for `1 ≤ z < z'` and `t < t'`,

under strict lower-triangularity, positivity on admissible edges, and
positive-column TP2 of the kernel.

Structure:
1. closure of `CoeffNonneg` under `0`, `1`, `C r` (`0 ≤ r`), `X j`, `+`,
   finite sums and products;
2. every entry of `T^t` is coefficientwise nonnegative;
3. a "doubled" finite Cauchy--Binet identity in a commutative ring;
4. induction on `t`.

Nothing here evaluates the activities at numbers and nothing bounds `k`.
-/

namespace CommonTime

variable {k : ℕ}

/-! ## 1. Closure lemmas for coefficientwise nonnegativity -/

/-- Coefficient extraction is additive. Stated locally through
    `MvPolynomial.coeffAddMonoidHom`, so it does not depend on the `simp` set. -/
theorem coeff_add_apply (p q : Poly k) (e : Fin (k + 1) →₀ ℕ) :
    (p + q).coeff e = p.coeff e + q.coeff e :=
  map_add (MvPolynomial.coeffAddMonoidHom e) p q

theorem coeff_zero_apply (e : Fin (k + 1) →₀ ℕ) : (0 : Poly k).coeff e = 0 :=
  map_zero (MvPolynomial.coeffAddMonoidHom e)

theorem coeffNonneg_zero : CoeffNonneg (0 : Poly k) := by
  intro e
  rw [coeff_zero_apply]

theorem coeffNonneg_C {r : ℝ} (hr : 0 ≤ r) :
    CoeffNonneg (MvPolynomial.C r : Poly k) := by
  intro e
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hr
  · exact le_refl 0

theorem coeffNonneg_one : CoeffNonneg (1 : Poly k) := by
  have h : (1 : Poly k) = MvPolynomial.C 1 := MvPolynomial.C_1.symm
  rw [h]
  exact coeffNonneg_C zero_le_one

theorem coeffNonneg_X (j : Vertex k) :
    CoeffNonneg (MvPolynomial.X j : Poly k) := by
  intro e
  rw [MvPolynomial.coeff_X]
  split_ifs
  · exact zero_le_one
  · exact le_refl 0

theorem coeffNonneg_add {p q : Poly k}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p + q) := by
  intro e
  rw [coeff_add_apply]
  exact add_nonneg (hp e) (hq e)

theorem coeffNonneg_mul {p q : Poly k}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p * q) := by
  intro e
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x.1) (hq x.2))

theorem coeffNonneg_sum {ι : Type*} (s : Finset ι) (f : ι → Poly k)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∑ i ∈ s, f i) := by
  intro e
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg (fun i hi => h i hi e)

/-- If `p + p` is coefficientwise nonnegative then so is `p`
    (the coefficients are real numbers). -/
theorem coeffNonneg_of_add_self {p : Poly k}
    (h : CoeffNonneg (p + p)) : CoeffNonneg p := by
  intro e
  have h2 := h e
  rw [coeff_add_apply] at h2
  linarith

/-! ## 2. The transition matrix and its powers -/

theorem coeffNonneg_activity (j : Vertex k) : CoeffNonneg (activity j) := by
  unfold activity
  split_ifs
  · exact coeffNonneg_one
  · exact coeffNonneg_X j

/-- A strictly lower-triangular kernel that is positive below the diagonal
    is entrywise nonnegative. -/
theorem kernel_nonneg {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (n j : Vertex k) : 0 ≤ K n j := by
  rcases lt_or_ge j n with h | h
  · exact le_of_lt (hpos n j h)
  · exact le_of_eq (htri n j h).symm

theorem transitionMatrix_apply (K : Vertex k → Vertex k → ℝ) (n j : Vertex k) :
    transitionMatrix k K n j = MvPolynomial.C (K n j) * activity j := rfl

theorem coeffNonneg_transitionMatrix {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (n j : Vertex k) : CoeffNonneg (transitionMatrix k K n j) := by
  rw [transitionMatrix_apply]
  exact coeffNonneg_mul (coeffNonneg_C (kernel_nonneg htri hpos n j))
    (coeffNonneg_activity j)

/-- Entries of `T` vanish on and above the diagonal. -/
theorem transitionMatrix_eq_zero {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) {n j : Vertex k} (h : n ≤ j) :
    transitionMatrix k K n j = 0 := by
  rw [transitionMatrix_apply, htri n j h, MvPolynomial.C_0, zero_mul]

/-- Every entry of every power of `T` is coefficientwise nonnegative. -/
theorem coeffNonneg_pow_entry {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (t : ℕ) (n z : Vertex k) :
    CoeffNonneg (((transitionMatrix k K) ^ t) n z) := by
  induction t generalizing n z with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact coeffNonneg_one
    · exact coeffNonneg_zero
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact coeffNonneg_sum _ _ (fun w _ =>
      coeffNonneg_mul (ih n w) (coeffNonneg_transitionMatrix htri hpos w z))

theorem coeffNonneg_backwardWeight {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (t : ℕ) (z : Vertex k) : CoeffNonneg (backwardWeight k t K z) :=
  coeffNonneg_pow_entry htri hpos t _ z

/-- One-step recursion `h_{t+1}(z) = ∑_w h_t(w) T(w,z)`. -/
theorem backwardWeight_succ (K : Vertex k → Vertex k → ℝ) (t : ℕ) (z : Vertex k) :
    backwardWeight k (t + 1) K z
      = ∑ w : Vertex k, backwardWeight k t K w * transitionMatrix k K w z := by
  unfold backwardWeight
  rw [pow_succ, Matrix.mul_apply]

/-- `h_0(z) = 0` unless `z` is the endpoint `k`. -/
theorem backwardWeight_zero_of_lt (K : Vertex k → Vertex k → ℝ)
    {z z' : Vertex k} (hzz' : z < z') : backwardWeight k 0 K z = 0 := by
  unfold backwardWeight
  rw [pow_zero]
  apply Matrix.one_apply_ne
  intro h
  have hk : z.val = k := congrArg Fin.val h.symm
  have h1 : z.val < z'.val := hzz'
  have h2 : z'.val < k + 1 := z'.isLt
  omega

/-! ## 3. Doubled Cauchy--Binet identity -/

/-- For finite families `a b c d` in a commutative ring,
    `2 * [(∑ a c)(∑ b d) - (∑ a d)(∑ b c)]`
    `  = ∑_{w,w'} (a_w b_{w'} - a_{w'} b_w)(c_w d_{w'} - c_{w'} d_w)`.
    Written with `E + E` so that no division or ordered-pair sum is needed. -/
theorem cauchy_binet_doubled {ι R : Type*} [Fintype ι] [CommRing R]
    (a b c d : ι → R) :
    ((∑ w, a w * c w) * (∑ w, b w * d w) - (∑ w, a w * d w) * (∑ w, b w * c w))
      + ((∑ w, a w * c w) * (∑ w, b w * d w)
          - (∑ w, a w * d w) * (∑ w, b w * c w))
    = ∑ w, ∑ w', (a w * b w' - a w' * b w) * (c w * d w' - c w' * d w) := by
  have h : ∀ w w', (a w * b w' - a w' * b w) * (c w * d w' - c w' * d w)
      = (a w * c w) * (b w' * d w') - (a w * d w) * (b w' * c w')
        - (b w * c w) * (a w' * d w') + (b w * d w) * (a w' * c w') := by
    intro w w'
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ## 4. The induction -/

/-- A single ordered term of the Cauchy--Binet expansion is coefficientwise
    nonnegative, given the inductive hypothesis at times `t < s`. -/
theorem backward_term_nonneg {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hK : PositiveColumnTP2 K)
    (t s : ℕ)
    (ih : ∀ y y' : Vertex k, 0 < y.val → y < y' →
      CoeffNonneg (backwardWeight k t K y' * backwardWeight k s K y -
        backwardWeight k t K y * backwardWeight k s K y'))
    (z z' : Vertex k) (hz0 : 0 < z.val) (hzz' : z < z')
    (u v : Vertex k) (huv : u < v) :
    CoeffNonneg
      ((backwardWeight k t K u * backwardWeight k s K v
          - backwardWeight k t K v * backwardWeight k s K u)
        * (transitionMatrix k K u z' * transitionMatrix k K v z
          - transitionMatrix k K v z' * transitionMatrix k K u z)) := by
  rcases le_or_gt u z with huz | hzu
  · -- `u ≤ z < z'`: both `T(u,z)` and `T(u,z')` vanish.
    have h1 : transitionMatrix k K u z = 0 := transitionMatrix_eq_zero htri huz
    have h2 : transitionMatrix k K u z' = 0 :=
      transitionMatrix_eq_zero htri (le_of_lt (lt_of_le_of_lt huz hzz'))
    rw [h1, h2, zero_mul, mul_zero, sub_zero, mul_zero]
    exact coeffNonneg_zero
  · -- `z < u < v`: inductive hypothesis at columns `(u,v)`, kernel minor at `(z,z')`.
    have hzu' : z.val < u.val := hzu
    have hu0 : 0 < u.val := lt_trans hz0 hzu'
    have hN := ih u v hu0 huv
    have hm : 0 ≤ K u z * K v z' - K u z' * K v z := hK u v z z' huv hzz' hz0
    have key :
        (backwardWeight k t K u * backwardWeight k s K v
            - backwardWeight k t K v * backwardWeight k s K u)
          * (transitionMatrix k K u z' * transitionMatrix k K v z
            - transitionMatrix k K v z' * transitionMatrix k K u z)
        = (backwardWeight k t K v * backwardWeight k s K u
            - backwardWeight k t K u * backwardWeight k s K v)
          * (MvPolynomial.C (K u z * K v z' - K u z' * K v z)
            * (activity z * activity z')) := by
      simp only [transitionMatrix_apply, map_sub, map_mul]
      ring
    rw [key]
    exact coeffNonneg_mul hN
      (coeffNonneg_mul (coeffNonneg_C hm)
        (coeffNonneg_mul (coeffNonneg_activity z) (coeffNonneg_activity z')))

/-- Induction form of manuscript Lemma 3.8 (positive-column hypothesis). -/
theorem backward_minor_aux {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K) (t : ℕ) :
    ∀ t' : ℕ, t < t' → ∀ z z' : Vertex k, 0 < z.val → z < z' →
      CoeffNonneg
        (backwardWeight k t K z' * backwardWeight k t' K z -
         backwardWeight k t K z * backwardWeight k t' K z') := by
  induction t with
  | zero =>
    intro t' _ z z' _ hzz'
    rw [backwardWeight_zero_of_lt K hzz', zero_mul, sub_zero]
    exact coeffNonneg_mul (coeffNonneg_backwardWeight htri hpos 0 z')
      (coeffNonneg_backwardWeight htri hpos t' z)
  | succ t ih =>
    intro t' htt' z z' hz0 hzz'
    obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := ⟨t' - 1, by omega⟩
    have hts : t < s := by omega
    have ih' := ih s hts
    rw [backwardWeight_succ K t z', backwardWeight_succ K s z,
      backwardWeight_succ K t z, backwardWeight_succ K s z']
    apply coeffNonneg_of_add_self
    rw [cauchy_binet_doubled (fun w => backwardWeight k t K w)
      (fun w => backwardWeight k s K w)
      (fun w => transitionMatrix k K w z')
      (fun w => transitionMatrix k K w z)]
    apply coeffNonneg_sum
    intro w _
    apply coeffNonneg_sum
    intro w' _
    rcases lt_trichotomy w w' with hlt | heq | hgt
    · exact backward_term_nonneg htri hK t s ih' z z' hz0 hzz' w w' hlt
    · subst heq
      rw [sub_self, zero_mul]
      exact coeffNonneg_zero
    · have hterm := backward_term_nonneg htri hK t s ih' z z' hz0 hzz' w' w hgt
      have e :
          (backwardWeight k t K w * backwardWeight k s K w'
              - backwardWeight k t K w' * backwardWeight k s K w)
            * (transitionMatrix k K w z' * transitionMatrix k K w' z
              - transitionMatrix k K w' z' * transitionMatrix k K w z)
          = (backwardWeight k t K w' * backwardWeight k s K w
              - backwardWeight k t K w * backwardWeight k s K w')
            * (transitionMatrix k K w' z' * transitionMatrix k K w z
              - transitionMatrix k K w z' * transitionMatrix k K w' z) := by
        ring
      rw [e]
      exact hterm

end CommonTime
