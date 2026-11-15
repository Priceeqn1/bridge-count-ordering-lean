import CommonTime.BackwardMinor

/-!
# First-crossing minors (manuscript Lemma 3.9)

`crossingWeight k theta q rho K z` is `E^theta_rho(z)`: the total weight of
`theta`-jump increasing paths `0 → z` whose vertex at time `rho` is `≤ q` and
whose vertex at time `rho + 1` is `> q`. This file proves

  `E_rho(z') * E_rho'(z) - E_rho(z) * E_rho'(z') ⪰ 0` coefficientwise,
  for `rho < rho' < theta` and `q < z < z'`,

under strict lower-triangularity, positivity on admissible edges and
positive-column TP2.

Structure:
1. `Fin.snoc` bookkeeping: admissibility, path weight and the crossing event
   for a path with one more jump appended;
2. the last-jump recursion for sums over explicit paths (`pathsTo_sum_succ`),
   and its three instances: all paths (`forwardWeight_succ`), crossing before
   the last jump (`crossingWeight_succ_lt`), crossing at the last jump
   (`crossingWeight_succ_last`);
3. vanishing lemmas obtained from the recursions;
4. a one-step transport lemma for reverse-rule families
   (`transport_minor_nonneg`), using the doubled Cauchy--Binet identity;
5. induction on `theta`.

Nothing here evaluates the activities at numbers and nothing bounds `k`.
-/

namespace CommonTime

variable {k : ℕ}

/-! ## 0. Further closure lemmas and auxiliary weights -/

theorem coeffNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → Poly k)
    (h : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∏ i ∈ s, f i) :=
  Finset.prod_induction f CoeffNonneg (fun _ _ ha hb => coeffNonneg_mul ha hb)
    coeffNonneg_one h

theorem coeffNonneg_stepWeight {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (n j : Vertex k) : CoeffNonneg (stepWeight K n j) := by
  unfold stepWeight
  exact coeffNonneg_mul (coeffNonneg_C (kernel_nonneg htri hpos n j))
    (coeffNonneg_activity j)

theorem stepWeight_eq_zero {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) {n j : Vertex k} (h : n ≤ j) :
    stepWeight K n j = 0 := by
  unfold stepWeight
  rw [htri n j h, MvPolynomial.C_0, zero_mul]

theorem coeffNonneg_pathWeight {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (m : ℕ) (p : Path k m) : CoeffNonneg (pathWeight k m K p) := by
  unfold pathWeight
  exact coeffNonneg_prod _ _ (fun i _ => coeffNonneg_stepWeight htri hpos _ _)

/-- `G^m(z)`: the total weight of all `m`-jump increasing paths `0 → z`. -/
noncomputable def forwardWeight (k m : ℕ)
    (K : Vertex k → Vertex k → ℝ) (z : Vertex k) : Poly k :=
  ∑ p ∈ pathsTo k m z, pathWeight k m K p

/-- `G^m(w)` restricted to endpoints `w ≤ q`. -/
noncomputable def cappedForward (k m q : ℕ)
    (K : Vertex k → Vertex k → ℝ) (w : Vertex k) : Poly k :=
  if w.val ≤ q then forwardWeight k m K w else 0

theorem coeffNonneg_forwardWeight {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (m : ℕ) (z : Vertex k) : CoeffNonneg (forwardWeight k m K z) := by
  unfold forwardWeight
  exact coeffNonneg_sum _ _ (fun p _ => coeffNonneg_pathWeight htri hpos m p)

theorem coeffNonneg_cappedForward {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (m q : ℕ) (w : Vertex k) : CoeffNonneg (cappedForward k m q K w) := by
  unfold cappedForward
  split_ifs
  · exact coeffNonneg_forwardWeight htri hpos m w
  · exact coeffNonneg_zero

theorem coeffNonneg_crossingWeight {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (m q rho : ℕ) (z : Vertex k) : CoeffNonneg (crossingWeight k m q rho K z) := by
  unfold crossingWeight
  apply coeffNonneg_sum
  intro p _
  split_ifs
  · exact coeffNonneg_pathWeight htri hpos m p
  · exact coeffNonneg_zero

/-! ## 1. Appending one jump to a path -/

theorem snoc_apply_lt {m : ℕ} (p : Path k m) (y : Vertex k) (j : ℕ)
    (hj : j < m + 1) {hj' : j < m + 1 + 1} :
    (Fin.snoc p y : Path k (m + 1)) ⟨j, hj'⟩ = p ⟨j, hj⟩ :=
  Fin.snoc_castSucc (α := fun _ => Vertex k) y p ⟨j, hj⟩

theorem snoc_apply_last {m : ℕ} (p : Path k m) (y : Vertex k)
    {h : m + 1 < m + 1 + 1} :
    (Fin.snoc p y : Path k (m + 1)) ⟨m + 1, h⟩ = y :=
  Fin.snoc_last (α := fun _ => Vertex k) y p

/-- A path with one more jump is admissible to `z` iff its initial segment is
    admissible to its own endpoint, the last jump is increasing, and the new
    endpoint is `z`. -/
theorem admissibleTo_snoc {m : ℕ} (p : Path k m) (y z : Vertex k) :
    admissibleTo k (m + 1) z (Fin.snoc p y : Path k (m + 1))
      ↔ admissibleTo k m (p (Fin.last m)) p ∧ p (Fin.last m) < y ∧ y = z := by
  unfold admissibleTo
  constructor
  · rintro ⟨h0, hend, hstep⟩
    rw [snoc_apply_lt p y 0 (Nat.zero_lt_succ m)] at h0
    rw [snoc_apply_last] at hend
    refine ⟨⟨h0, rfl, fun i => ?_⟩, ?_, hend⟩
    · have h1 : (Fin.snoc p y : Path k (m + 1)) ⟨i.val, Nat.lt_succ_of_lt (Nat.lt_succ_of_lt i.isLt)⟩
          < (Fin.snoc p y : Path k (m + 1)) ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt i.isLt)⟩ :=
        hstep ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      rw [snoc_apply_lt p y i.val (Nat.lt_succ_of_lt i.isLt),
        snoc_apply_lt p y (i.val + 1) (Nat.succ_lt_succ i.isLt)] at h1
      exact h1
    · have h1 : (Fin.snoc p y : Path k (m + 1)) ⟨m, Nat.lt_succ_of_lt (Nat.lt_succ_self m)⟩
          < (Fin.snoc p y : Path k (m + 1)) ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ :=
        hstep ⟨m, Nat.lt_succ_self m⟩
      rw [snoc_apply_lt p y m (Nat.lt_succ_self m), snoc_apply_last] at h1
      exact h1
  · rintro ⟨⟨h0, -, hstep⟩, hlt, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [snoc_apply_lt p y 0 (Nat.zero_lt_succ m)]
      exact h0
    · rw [snoc_apply_last]
    · rintro ⟨j, hj⟩
      show (Fin.snoc p y : Path k (m + 1)) ⟨j, Nat.lt_succ_of_lt hj⟩
        < (Fin.snoc p y : Path k (m + 1)) ⟨j + 1, Nat.succ_lt_succ hj⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjm | hjm
      · rw [snoc_apply_lt p y j (Nat.lt_succ_of_lt hjm),
          snoc_apply_lt p y (j + 1) (Nat.succ_lt_succ hjm)]
        exact hstep ⟨j, hjm⟩
      · subst hjm
        rw [snoc_apply_lt p y j (Nat.lt_succ_self j), snoc_apply_last]
        exact hlt

/-- The weight of a path with one more jump. -/
theorem pathWeight_snoc (K : Vertex k → Vertex k → ℝ) {m : ℕ}
    (p : Path k m) (y : Vertex k) :
    pathWeight k (m + 1) K (Fin.snoc p y : Path k (m + 1))
      = pathWeight k m K p * stepWeight K y (p (Fin.last m)) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have h1 : (Fin.snoc p y : Path k (m + 1)) (Fin.castSucc i).succ = p i.succ :=
      snoc_apply_lt p y (i.val + 1) (Nat.succ_lt_succ i.isLt)
    have h2 : (Fin.snoc p y : Path k (m + 1)) (Fin.castSucc i).castSucc = p i.castSucc :=
      snoc_apply_lt p y i.val (Nat.lt_succ_of_lt i.isLt)
    rw [h1, h2]
  · have h1 : (Fin.snoc p y : Path k (m + 1)) (Fin.last m).succ = y :=
      snoc_apply_last p y
    have h2 : (Fin.snoc p y : Path k (m + 1)) (Fin.last m).castSucc = p (Fin.last m) :=
      snoc_apply_lt p y m (Nat.lt_succ_self m)
    rw [h1, h2]

/-- A crossing strictly before the appended jump is a crossing of the
    initial segment. -/
theorem crossesAt_snoc_lt {m : ℕ} (q rho : ℕ) (hr : rho < m)
    (p : Path k m) (y : Vertex k) :
    crossesAt k (m + 1) q rho (Fin.snoc p y : Path k (m + 1))
      ↔ crossesAt k m q rho p := by
  unfold crossesAt
  constructor
  · rintro ⟨h, h1, h2⟩
    rw [snoc_apply_lt p y rho (Nat.lt_succ_of_lt hr)] at h1
    rw [snoc_apply_lt p y (rho + 1) (Nat.succ_lt_succ hr)] at h2
    exact ⟨hr, h1, h2⟩
  · rintro ⟨h, h1, h2⟩
    refine ⟨Nat.lt_succ_of_lt hr, ?_, ?_⟩
    · rw [snoc_apply_lt p y rho (Nat.lt_succ_of_lt hr)]
      exact h1
    · rw [snoc_apply_lt p y (rho + 1) (Nat.succ_lt_succ hr)]
      exact h2

/-- A crossing at the appended jump. -/
theorem crossesAt_snoc_last {m : ℕ} (q : ℕ) (p : Path k m) (y : Vertex k) :
    crossesAt k (m + 1) q m (Fin.snoc p y : Path k (m + 1))
      ↔ (p (Fin.last m)).val ≤ q ∧ q < y.val := by
  unfold crossesAt
  constructor
  · rintro ⟨h, h1, h2⟩
    rw [snoc_apply_lt p y m (Nat.lt_succ_self m)] at h1
    rw [snoc_apply_last] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Nat.lt_succ_self m, ?_, ?_⟩
    · rw [snoc_apply_lt p y m (Nat.lt_succ_self m)]
      exact h1
    · rw [snoc_apply_last]
      exact h2

/-! ## 2. The last-jump recursion for path sums -/

/-- A sum over all `(m+1)`-jump vertex sequences, reindexed by the initial
    segment and the last vertex. -/
theorem sum_path_succ {m : ℕ} (F : Path k (m + 1) → Poly k) :
    ∑ p : Path k (m + 1), F p
      = ∑ p' : Path k m, ∑ y : Vertex k, F (Fin.snoc p' y : Path k (m + 1)) := by
  rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type
    (f := fun x : Vertex k × Path k m => F (Fin.snoc x.2 x.1 : Path k (m + 1)))]
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m + 1 + 1) => Vertex k))
    (fun x : Vertex k × Path k m => F (Fin.snoc x.2 x.1 : Path k (m + 1))) F
    (fun _ => rfl)).symm

open Classical in
/-- Last-jump recursion for a sum over admissible paths restricted by an
    event `φ`. The event for the extended path is described by `ψ` on the
    initial segment and its endpoint `w`. No constraint `w < z` is needed on
    the right-hand side because `stepWeight K z w = 0` for `z ≤ w`. -/
theorem pathsTo_sum_succ {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) {m : ℕ} (z : Vertex k)
    (φ : Path k (m + 1) → Prop) (ψ : Vertex k → Path k m → Prop)
    (hφ : ∀ (w : Vertex k) (p' : Path k m), admissibleTo k m w p' →
      (φ (Fin.snoc p' z : Path k (m + 1)) ↔ ψ w p')) :
    (∑ p ∈ pathsTo k (m + 1) z, if φ p then pathWeight k (m + 1) K p else 0)
      = ∑ w : Vertex k, ∑ p' ∈ pathsTo k m w,
          if ψ w p' then pathWeight k m K p' * stepWeight K z w else 0 := by
  unfold pathsTo
  rw [Finset.sum_filter, sum_path_succ]
  have hR : (∑ w : Vertex k, ∑ p' ∈ Finset.univ.filter (admissibleTo k m w),
        if ψ w p' then pathWeight k m K p' * stepWeight K z w else 0)
      = ∑ p' : Path k m, ∑ w : Vertex k,
          if admissibleTo k m w p' then
            (if ψ w p' then pathWeight k m K p' * stepWeight K z w else 0) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_filter]
  rw [hR]
  apply Finset.sum_congr rfl
  intro p' _
  -- left: only `y = z` contributes
  have hL1 : (∑ y : Vertex k,
        if admissibleTo k (m + 1) z (Fin.snoc p' y : Path k (m + 1)) then
          (if φ (Fin.snoc p' y : Path k (m + 1)) then
            pathWeight k (m + 1) K (Fin.snoc p' y : Path k (m + 1)) else 0) else 0)
      = if admissibleTo k (m + 1) z (Fin.snoc p' z : Path k (m + 1)) then
          (if φ (Fin.snoc p' z : Path k (m + 1)) then
            pathWeight k (m + 1) K (Fin.snoc p' z : Path k (m + 1)) else 0) else 0 := by
    apply Fintype.sum_eq_single z
    intro y hy
    apply ite_eq_right
    intro hadm
    exact hy ((admissibleTo_snoc p' y z).mp hadm).2.2
  -- right: only `w = p' (last m)` contributes
  have hR1 : (∑ w : Vertex k,
        if admissibleTo k m w p' then
          (if ψ w p' then pathWeight k m K p' * stepWeight K z w else 0) else 0)
      = if admissibleTo k m (p' (Fin.last m)) p' then
          (if ψ (p' (Fin.last m)) p' then
            pathWeight k m K p' * stepWeight K z (p' (Fin.last m)) else 0) else 0 := by
    apply Fintype.sum_eq_single (p' (Fin.last m))
    intro w hw
    apply ite_eq_right
    intro hadm
    exact hw hadm.2.1.symm
  rw [hL1, hR1]
  by_cases hadm : admissibleTo k m (p' (Fin.last m)) p'
  · by_cases hlt : p' (Fin.last m) < z
    · have hadm' : admissibleTo k (m + 1) z (Fin.snoc p' z : Path k (m + 1)) :=
        (admissibleTo_snoc p' z z).mpr ⟨hadm, hlt, rfl⟩
      rw [ite_eq_left hadm', ite_eq_left hadm, pathWeight_snoc]
      by_cases hψ : ψ (p' (Fin.last m)) p'
      · rw [ite_eq_left hψ, ite_eq_left ((hφ _ p' hadm).mpr hψ)]
      · rw [ite_eq_right hψ, ite_eq_right (fun h => hψ ((hφ _ p' hadm).mp h))]
    · have hnadm : ¬ admissibleTo k (m + 1) z (Fin.snoc p' z : Path k (m + 1)) :=
        fun h => hlt ((admissibleTo_snoc p' z z).mp h).2.1
      rw [ite_eq_right hnadm, ite_eq_left hadm,
        stepWeight_eq_zero htri (le_of_not_gt hlt), mul_zero]
      split_ifs <;> rfl
  · have hnadm : ¬ admissibleTo k (m + 1) z (Fin.snoc p' z : Path k (m + 1)) :=
      fun h => hadm ((admissibleTo_snoc p' z z).mp h).1
    rw [ite_eq_right hnadm, ite_eq_right hadm]

/-- `G^{m+1}(z) = ∑_w G^m(w) * T(z,w)`. -/
theorem forwardWeight_succ {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (m : ℕ) (z : Vertex k) :
    forwardWeight k (m + 1) K z
      = ∑ w : Vertex k, forwardWeight k m K w * stepWeight K z w := by
  classical
  unfold forwardWeight
  have h := pathsTo_sum_succ (K := K) htri (m := m) z (fun _ => True) (fun _ _ => True)
    (fun _ _ _ => Iff.rfl)
  refine (Finset.sum_congr rfl (fun p _ => ?_)).trans (h.trans ?_)
  · exact (ite_eq_left trivial).symm
  · apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p' _ => ite_eq_left trivial)

/-- For `rho < m`: `E^{m+1}_rho(z) = ∑_w E^m_rho(w) * T(z,w)`. -/
theorem crossingWeight_succ_lt {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) {m : ℕ} (q rho : ℕ) (hr : rho < m)
    (z : Vertex k) :
    crossingWeight k (m + 1) q rho K z
      = ∑ w : Vertex k, crossingWeight k m q rho K w * stepWeight K z w := by
  classical
  unfold crossingWeight
  rw [pathsTo_sum_succ (K := K) htri z (fun p => crossesAt k (m + 1) q rho p)
    (fun _ p' => crossesAt k m q rho p')
    (fun _ p' _ => crossesAt_snoc_lt q rho hr p' z)]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p' _
  by_cases h : crossesAt k m q rho p'
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, zero_mul]

/-- Crossing at the last jump:
    `E^{m+1}_m(z) = ∑_{w ≤ q} G^m(w) * T(z,w)` if `q < z`, and `0` otherwise. -/
theorem crossingWeight_succ_last {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (m q : ℕ) (z : Vertex k) :
    crossingWeight k (m + 1) q m K z
      = if q < z.val then
          ∑ w : Vertex k, cappedForward k m q K w * stepWeight K z w
        else 0 := by
  classical
  unfold crossingWeight
  rw [pathsTo_sum_succ (K := K) htri z (fun p => crossesAt k (m + 1) q m p)
    (fun w _ => w.val ≤ q ∧ q < z.val)
    (fun w p' hadm => by
      have hw : p' (Fin.last m) = w := hadm.2.1
      rw [crossesAt_snoc_last, hw])]
  by_cases hqz : q < z.val
  · rw [ite_eq_left hqz]
    apply Finset.sum_congr rfl
    intro w _
    unfold cappedForward forwardWeight
    by_cases hw : w.val ≤ q
    · rw [ite_eq_left hw, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun p' _ => ite_eq_left ⟨hw, hqz⟩)
    · rw [ite_eq_right hw, zero_mul]
      exact Finset.sum_eq_zero (fun p' _ => ite_eq_right (fun h => hw h.1))
  · rw [ite_eq_right hqz]
    exact Finset.sum_eq_zero (fun w _ =>
      Finset.sum_eq_zero (fun p' _ => ite_eq_right (fun h => hqz h.2)))

/-! ## 3. Vanishing lemmas -/

/-- No path with at least one jump ends at state `0`. -/
theorem forwardWeight_eq_zero_of_val_zero {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (m : ℕ) (hm : 0 < m)
    (z : Vertex k) (hz : z.val = 0) : forwardWeight k m K z = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [forwardWeight_succ htri]
  apply Finset.sum_eq_zero
  intro w _
  have hzw : z ≤ w := by
    have h : z.val ≤ w.val := by omega
    exact h
  rw [stepWeight_eq_zero htri hzw, mul_zero]

theorem cappedForward_eq_zero_of_val_zero {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (m q : ℕ) (hm : 0 < m)
    (w : Vertex k) (hw : w.val = 0) : cappedForward k m q K w = 0 := by
  unfold cappedForward
  split_ifs
  · exact forwardWeight_eq_zero_of_val_zero htri m hm w hw
  · rfl

/-- A path that has crossed above `q` cannot end at a state `≤ q`. -/
theorem crossingWeight_eq_zero_of_le {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (q : ℕ) (m : ℕ) :
    ∀ (rho : ℕ) (z : Vertex k), rho < m → z.val ≤ q →
      crossingWeight k m q rho K z = 0 := by
  induction m with
  | zero =>
    intro rho z hr _
    exact absurd hr (Nat.not_lt_zero rho)
  | succ m ih =>
    intro rho z hr hzq
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | heq
    · rw [crossingWeight_succ_lt htri q rho hlt z]
      apply Finset.sum_eq_zero
      intro w _
      by_cases hwz : w < z
      · have hwz' : w.val < z.val := hwz
        rw [ih rho w hlt (by omega), zero_mul]
      · rw [stepWeight_eq_zero htri (le_of_not_gt hwz), mul_zero]
    · rw [heq, crossingWeight_succ_last htri m q z]
      exact ite_eq_right (by omega)

/-! ## 4. One-step transport of reverse-rule families -/

/-- One ordered term of the Cauchy--Binet expansion in the transport step. -/
theorem transport_term_nonneg {K : Vertex k → Vertex k → ℝ}
    (hK : PositiveColumnTP2 K) (a b : Vertex k → Poly k)
    (h0 : ∀ w : Vertex k, w.val = 0 → a w = 0 ∧ b w = 0)
    (hrev : ∀ w w' : Vertex k, w < w' → CoeffNonneg (a w' * b w - a w * b w'))
    (z z' : Vertex k) (hzz' : z < z') (w w' : Vertex k) (hww' : w < w') :
    CoeffNonneg
      ((a w * b w' - a w' * b w)
        * (stepWeight K z' w * stepWeight K z w'
          - stepWeight K z' w' * stepWeight K z w)) := by
  by_cases hw0 : w.val = 0
  · rw [(h0 w hw0).1, (h0 w hw0).2, zero_mul, mul_zero, sub_zero, zero_mul]
    exact coeffNonneg_zero
  · have hw0' : 0 < w.val := Nat.pos_of_ne_zero hw0
    have hm : 0 ≤ K z w * K z' w' - K z w' * K z' w := hK z z' w w' hzz' hww' hw0'
    have key :
        (a w * b w' - a w' * b w)
          * (stepWeight K z' w * stepWeight K z w'
            - stepWeight K z' w' * stepWeight K z w)
        = (a w' * b w - a w * b w')
          * (MvPolynomial.C (K z w * K z' w' - K z w' * K z' w)
            * (activity w * activity w')) := by
      unfold stepWeight
      simp only [map_sub, map_mul]
      ring
    rw [key]
    exact coeffNonneg_mul (hrev w w' hww')
      (coeffNonneg_mul (coeffNonneg_C hm)
        (coeffNonneg_mul (coeffNonneg_activity w) (coeffNonneg_activity w')))

/-- If the family `(a, b)` is reverse-rule in the state variable and both
    vanish at state `0`, then so is the family obtained by one more jump
    through a positive-column TP2 kernel. -/
theorem transport_minor_nonneg {K : Vertex k → Vertex k → ℝ}
    (hK : PositiveColumnTP2 K) (a b : Vertex k → Poly k)
    (h0 : ∀ w : Vertex k, w.val = 0 → a w = 0 ∧ b w = 0)
    (hrev : ∀ w w' : Vertex k, w < w' → CoeffNonneg (a w' * b w - a w * b w'))
    (z z' : Vertex k) (hzz' : z < z') :
    CoeffNonneg
      ((∑ w : Vertex k, a w * stepWeight K z' w)
          * (∑ w : Vertex k, b w * stepWeight K z w)
        - (∑ w : Vertex k, a w * stepWeight K z w)
          * (∑ w : Vertex k, b w * stepWeight K z' w)) := by
  apply coeffNonneg_of_add_self
  rw [cauchy_binet_doubled a b (fun w => stepWeight K z' w) (fun w => stepWeight K z w)]
  apply coeffNonneg_sum
  intro w _
  apply coeffNonneg_sum
  intro w' _
  rcases lt_trichotomy w w' with hlt | heq | hgt
  · exact transport_term_nonneg hK a b h0 hrev z z' hzz' w w' hlt
  · subst heq
    rw [sub_self, zero_mul]
    exact coeffNonneg_zero
  · have hterm := transport_term_nonneg hK a b h0 hrev z z' hzz' w' w hgt
    have e :
        (a w * b w' - a w' * b w)
          * (stepWeight K z' w * stepWeight K z w'
            - stepWeight K z' w' * stepWeight K z w)
        = (a w' * b w - a w * b w')
          * (stepWeight K z' w' * stepWeight K z w
            - stepWeight K z' w * stepWeight K z w') := by
      ring
    rw [e]
    exact hterm

/-! ## 5. The induction on the number of jumps -/

/-- Induction form of manuscript Lemma 3.9. -/
theorem crossing_minor_aux {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K) (q : ℕ) (theta : ℕ) :
    ∀ rho rho' : ℕ, rho < rho' → rho' < theta →
      ∀ z z' : Vertex k, q < z.val → z < z' →
        CoeffNonneg
          (crossingWeight k theta q rho K z' * crossingWeight k theta q rho' K z -
           crossingWeight k theta q rho K z * crossingWeight k theta q rho' K z') := by
  induction theta with
  | zero =>
    intro rho rho' _ h
    exact absurd h (Nat.not_lt_zero rho')
  | succ m ih =>
    intro rho rho' hrr' hr' z z' hqz hzz'
    have hr : rho < m := by omega
    have hm : 0 < m := by omega
    have hzz'v : z.val < z'.val := hzz'
    have hqz' : q < z'.val := by omega
    rw [crossingWeight_succ_lt htri q rho hr z', crossingWeight_succ_lt htri q rho hr z]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr') with hlt | heq
    · -- both crossings occur before the last jump: inductive hypothesis
      rw [crossingWeight_succ_lt htri q rho' hlt z, crossingWeight_succ_lt htri q rho' hlt z']
      apply transport_minor_nonneg hK (fun w => crossingWeight k m q rho K w)
        (fun w => crossingWeight k m q rho' K w)
      · intro w hw
        exact ⟨crossingWeight_eq_zero_of_le htri q m rho w hr (by omega),
          crossingWeight_eq_zero_of_le htri q m rho' w hlt (by omega)⟩
      · intro w w' hww'
        by_cases hqw : q < w.val
        · exact ih rho rho' hrr' hlt w w' hqw hww'
        · rw [crossingWeight_eq_zero_of_le htri q m rho w hr (by omega),
            crossingWeight_eq_zero_of_le htri q m rho' w hlt (by omega),
            mul_zero, zero_mul, sub_zero]
          exact coeffNonneg_zero
      · exact hzz'
    · -- the later crossing is the last jump: disjoint supports
      rw [heq, crossingWeight_succ_last htri m q z, crossingWeight_succ_last htri m q z',
        ite_eq_left hqz, ite_eq_left hqz']
      apply transport_minor_nonneg hK (fun w => crossingWeight k m q rho K w)
        (fun w => cappedForward k m q K w)
      · intro w hw
        exact ⟨crossingWeight_eq_zero_of_le htri q m rho w hr (by omega),
          cappedForward_eq_zero_of_val_zero htri m q hm w hw⟩
      · intro w w' hww'
        have hww'v : w.val < w'.val := hww'
        have hz : crossingWeight k m q rho K w * cappedForward k m q K w' = 0 := by
          by_cases hw' : w'.val ≤ q
          · rw [crossingWeight_eq_zero_of_le htri q m rho w hr (by omega), zero_mul]
          · unfold cappedForward
            rw [ite_eq_right hw', mul_zero]
        rw [hz, sub_zero]
        exact coeffNonneg_mul (coeffNonneg_crossingWeight htri hpos m q rho w')
          (coeffNonneg_cappedForward htri hpos m q w)
      · exact hzz'

end CommonTime
