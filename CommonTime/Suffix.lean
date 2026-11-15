import CommonTime.LogConcavity

/-!
# Suffix count arrays (manuscript Theorem 3.10, two-sided clause)

`suffixArray k q r s K` is the total weight of increasing paths `0 → k` with
`r` intermediate vertices, exactly `s` of which lie in `[q, k-1]`. This file
proves that its ordered `2 × 2` minors are coefficientwise nonnegative:

  `H(r,s) * H(r',s') - H(r,s') * H(r',s) ⪰ 0` for `r < r'`, `s < s'`,

under strict lower-triangularity, positivity on admissible edges, full TP2
and `1 ≤ q < k`.

A vertex equal to `q` counts as a suffix visit, so the relevant crossing is
of level `q - 1`; this is where `1 ≤ q` is used.

Structure:
1. a path crossing above `q - 1` at jump `ρ + 1` has exactly `m - 1 - ρ`
   intermediate vertices `≥ q`; hence
   `suffixArray k q r s K = crossingWeight k (r+1) (q-1) (r-s) K k` for `s ≤ r`
   and `0` otherwise (`suffixArray_eq`);
2. the forward weights `G^t(z)` are coefficientwise TP2 in `(t,z)`
   (`forward_minor`);
3. the part of a path from the crossing onward is packaged algebraically:
   `suffixCore` (cross immediately, then `t` further jumps to `k`) and
   `suffixTail` (`j` jumps below the level first); `suffixTail` is
   coefficientwise TP2 in the pair (number of visits, state)
   (`suffixTail_minor`);
4. common-time split measured from the end of the path (`suffix_split`) and
   the theorem, through the doubled Cauchy--Binet identity.

No reflection of the state space is used: the argument is the mirror image
of the prefix argument, carried out directly.
Nothing here evaluates the activities at numbers and nothing bounds `k`.
-/

namespace CommonTime

variable {k : ℕ}

/-! ## 0. Generic tools -/

/-- Doubled Cauchy--Binet with a termwise sign hypothesis on ordered pairs. -/
theorem doubled_sum_nonneg (a b c d : Vertex k → Poly k)
    (h : ∀ w w' : Vertex k, w < w' →
      CoeffNonneg ((a w * b w' - a w' * b w) * (c w * d w' - c w' * d w))) :
    CoeffNonneg
      ((∑ w : Vertex k, a w * c w) * (∑ w : Vertex k, b w * d w)
        - (∑ w : Vertex k, a w * d w) * (∑ w : Vertex k, b w * c w)) := by
  apply coeffNonneg_of_add_self
  rw [cauchy_binet_doubled a b c d]
  apply coeffNonneg_sum
  intro w _
  apply coeffNonneg_sum
  intro w' _
  rcases lt_trichotomy w w' with hlt | heq | hgt
  · exact h w w' hlt
  · subst heq
    rw [sub_self, zero_mul]
    exact coeffNonneg_zero
  · have hterm := h w' w hgt
    have e : (a w * b w' - a w' * b w) * (c w * d w' - c w' * d w)
        = (a w' * b w - a w * b w') * (c w' * d w - c w * d w') := by
      ring
    rw [e]
    exact hterm

/-- Row transport under full TP2: a coefficientwise TP2 pair `(a, b)` in the
    state variable stays TP2 after one more jump `w → z`. -/
theorem row_transport_full {K : Vertex k → Vertex k → ℝ}
    (hK : FullTP2 K) (a b : Vertex k → Poly k)
    (hfwd : ∀ w w' : Vertex k, w < w' → CoeffNonneg (a w * b w' - a w' * b w))
    (z z' : Vertex k) (hzz' : z < z') :
    CoeffNonneg
      ((∑ w : Vertex k, a w * stepWeight K z w)
          * (∑ w : Vertex k, b w * stepWeight K z' w)
        - (∑ w : Vertex k, a w * stepWeight K z' w)
          * (∑ w : Vertex k, b w * stepWeight K z w)) := by
  apply doubled_sum_nonneg a b (fun w => stepWeight K z w) (fun w => stepWeight K z' w)
  intro w w' hww'
  have hm : 0 ≤ K z w * K z' w' - K z w' * K z' w := hK z z' w w' hzz' hww'
  have key : stepWeight K z w * stepWeight K z' w' - stepWeight K z w' * stepWeight K z' w
      = MvPolynomial.C (K z w * K z' w' - K z w' * K z' w)
        * (activity w * activity w') := by
    unfold stepWeight
    simp only [map_sub, map_mul]
    ring
  rw [key]
  exact coeffNonneg_mul (hfwd w w' hww')
    (coeffNonneg_mul (coeffNonneg_C hm)
      (coeffNonneg_mul (coeffNonneg_activity w) (coeffNonneg_activity w')))

/-- Column transport under full TP2: a coefficientwise TP2 pair `(c, e)` in
    the state variable stays TP2 after one more jump `z → v` prepended. -/
theorem col_transport_full {K : Vertex k → Vertex k → ℝ}
    (hK : FullTP2 K) (c e : Vertex k → Poly k)
    (hfwd : ∀ v x : Vertex k, v < x → CoeffNonneg (c v * e x - c x * e v))
    (z z' : Vertex k) (hzz' : z < z') :
    CoeffNonneg
      ((∑ v : Vertex k, c v * transitionMatrix k K v z)
          * (∑ v : Vertex k, e v * transitionMatrix k K v z')
        - (∑ v : Vertex k, c v * transitionMatrix k K v z')
          * (∑ v : Vertex k, e v * transitionMatrix k K v z)) := by
  apply doubled_sum_nonneg c e (fun v => transitionMatrix k K v z)
    (fun v => transitionMatrix k K v z')
  intro v x hvx
  have hm : 0 ≤ K v z * K x z' - K v z' * K x z := hK v x z z' hvx hzz'
  have key : transitionMatrix k K v z * transitionMatrix k K x z'
        - transitionMatrix k K x z * transitionMatrix k K v z'
      = MvPolynomial.C (K v z * K x z' - K v z' * K x z)
        * (activity z * activity z') := by
    simp only [transitionMatrix_apply, map_sub, map_mul]
    ring
  rw [key]
  exact coeffNonneg_mul (hfwd v x hvx)
    (coeffNonneg_mul (coeffNonneg_C hm)
      (coeffNonneg_mul (coeffNonneg_activity z) (coeffNonneg_activity z')))

/-- Powers of the transition matrix vanish strictly above the diagonal. -/
theorem pow_entry_eq_zero_of_lt {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (j : ℕ) :
    ∀ w v : Vertex k, w < v → ((transitionMatrix k K) ^ j) w v = 0 := by
  induction j with
  | zero =>
    intro w v hwv
    rw [pow_zero]
    exact Matrix.one_apply_ne (ne_of_lt hwv)
  | succ j ih =>
    intro w v hwv
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro u _
    by_cases huv : u ≤ v
    · rw [transitionMatrix_eq_zero htri huv, mul_zero]
    · rw [ih w u (lt_trans hwv (lt_of_not_ge huv)), zero_mul]

/-! ## 1. Suffix visits and the crossing of level `q - 1` -/

/-- The number of indices `ρ < i < m` in `Fin (m+1)`. -/
theorem card_between {m ρ : ℕ} :
    (Finset.univ.filter (fun i : Fin (m + 1) => ρ < i.val ∧ i.val < m)).card
      = m - ρ - 1 := by
  have hmap : (Finset.univ.filter (fun i : Fin (m + 1) => ρ < i.val ∧ i.val < m)).map
      Fin.valEmbedding = Finset.Ioo ρ m := by
    ext j
    rw [Finset.mem_map, Finset.mem_Ioo]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hj
      exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ioo]

/-- A strictly monotone path that crosses above `q - 1` at jump `ρ + 1` has
    exactly `m - 1 - ρ` intermediate vertices `≥ q`. -/
theorem suffixVisits_eq_of_crossesAt {m : ℕ} {p : Path k m} (q ρ : ℕ)
    (hq0 : 1 ≤ q) (hmono : StrictMono p) (hc : crossesAt k m (q - 1) ρ p) :
    suffixVisits k m q p = m - ρ - 1 := by
  obtain ⟨hρ, h1, h2⟩ := hc
  have hS : ∀ i : Fin (m + 1),
      (0 < i.val ∧ i.val < m ∧ q ≤ (p i).val) ↔ (ρ < i.val ∧ i.val < m) := by
    intro i
    constructor
    · rintro ⟨_, him, hiq⟩
      refine ⟨?_, him⟩
      by_contra hcon
      have hle : i ≤ (⟨ρ, Nat.lt_succ_of_lt hρ⟩ : Fin (m + 1)) :=
        Fin.le_def.mpr (by show i.val ≤ ρ; omega)
      have hp : (p i).val ≤ (p ⟨ρ, Nat.lt_succ_of_lt hρ⟩).val :=
        Fin.le_def.mp (hmono.monotone hle)
      omega
    · rintro ⟨hρi, him⟩
      have hle : (⟨ρ + 1, Nat.succ_lt_succ hρ⟩ : Fin (m + 1)) ≤ i :=
        Fin.le_def.mpr (by show ρ + 1 ≤ i.val; omega)
      have hp : (p ⟨ρ + 1, Nat.succ_lt_succ hρ⟩).val ≤ (p i).val :=
        Fin.le_def.mp (hmono.monotone hle)
      exact ⟨by omega, him, by omega⟩
  unfold suffixVisits
  rw [Finset.filter_congr (fun i _ => hS i)]
  exact card_between

/-- Suffix arrays are crossing weights of level `q - 1` at the endpoint `k`. -/
theorem suffixArray_eq (K : Vertex k → Vertex k → ℝ)
    (q : ℕ) (hq0 : 1 ≤ q) (hqk : q < k) (r s : ℕ) :
    suffixArray k q r s K
      = if s ≤ r then
          crossingWeight k (r + 1) (q - 1) (r - s) K ⟨k, Nat.lt_succ_self k⟩
        else 0 := by
  classical
  unfold suffixArray
  rw [paths_eq_pathsTo]
  have hpath : ∀ p ∈ pathsTo k (r + 1) ⟨k, Nat.lt_succ_self k⟩,
      ∃ ρ, ρ < r + 1 ∧ crossesAt k (r + 1) (q - 1) ρ p
        ∧ suffixVisits k (r + 1) q p = r + 1 - ρ - 1 := by
    intro p hp
    have hadm : admissibleTo k (r + 1) ⟨k, Nat.lt_succ_self k⟩ p := by
      unfold pathsTo at hp
      exact (Finset.mem_filter.mp hp).2
    have hqk' : q - 1 < (⟨k, Nat.lt_succ_self k⟩ : Vertex k).val := by
      show q - 1 < k
      omega
    obtain ⟨ρ, hρ⟩ := exists_crossesAt (q - 1) hadm hqk'
    have hlt : ρ < r + 1 := by
      obtain ⟨h, _⟩ := hρ
      exact h
    exact ⟨ρ, hlt, hρ,
      suffixVisits_eq_of_crossesAt q ρ hq0 (admissibleTo_strictMono hadm) hρ⟩
  by_cases hsr : s ≤ r
  · rw [ite_eq_left hsr]
    unfold crossingWeight
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨ρ, hlt, hρ, hv⟩ := hpath p hp
    have hadm : admissibleTo k (r + 1) ⟨k, Nat.lt_succ_self k⟩ p := by
      unfold pathsTo at hp
      exact (Finset.mem_filter.mp hp).2
    by_cases hc : crossesAt k (r + 1) (q - 1) (r - s) p
    · have hv' := suffixVisits_eq_of_crossesAt q (r - s) hq0
        (admissibleTo_strictMono hadm) hc
      have hs : suffixVisits k (r + 1) q p = s := by omega
      rw [ite_eq_left hc, ite_eq_left hs]
    · have hs : ¬ suffixVisits k (r + 1) q p = s := by
        intro hs
        have e : r - s = ρ := by omega
        rw [e] at hc
        exact hc hρ
      rw [ite_eq_right hc, ite_eq_right hs]
  · rw [ite_eq_right hsr]
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨ρ, hlt, hρ, hv⟩ := hpath p hp
    apply ite_eq_right
    omega

theorem coeffNonneg_suffixArray {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (q r s : ℕ) : CoeffNonneg (suffixArray k q r s K) := by
  classical
  unfold suffixArray
  apply coeffNonneg_sum
  intro p _
  split_ifs
  · exact coeffNonneg_pathWeight htri hpos (r + 1) p
  · exact coeffNonneg_zero

/-! ## 2. Forward weights are coefficientwise TP2 in (time, state) -/

/-- `G^t(z) * G^{t'}(z') - G^t(z') * G^{t'}(z) ⪰ 0` for `t < t'`, `z < z'`. -/
theorem forward_minor {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : FullTP2 K) (t : ℕ) :
    ∀ t' : ℕ, t < t' → ∀ z z' : Vertex k, z < z' →
      CoeffNonneg
        (forwardWeight k t K z * forwardWeight k t' K z'
          - forwardWeight k t K z' * forwardWeight k t' K z) := by
  induction t with
  | zero =>
    intro t' _ z z' hzz'
    have hz' : z' ≠ (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) := by
      intro h
      have h1 : z.val < z'.val := hzz'
      have h2 : z'.val = 0 := congrArg Fin.val h
      omega
    rw [forwardWeight_zero K z', Matrix.one_apply_ne hz', zero_mul, sub_zero]
    exact coeffNonneg_mul (coeffNonneg_forwardWeight htri hpos 0 z)
      (coeffNonneg_forwardWeight htri hpos t' z')
  | succ t ih =>
    intro t' htt' z z' hzz'
    obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := ⟨t' - 1, by omega⟩
    rw [forwardWeight_succ htri t z, forwardWeight_succ htri s z',
      forwardWeight_succ htri t z', forwardWeight_succ htri s z]
    exact row_transport_full hK (fun w => forwardWeight k t K w)
      (fun w => forwardWeight k s K w) (ih s (by omega)) z z' hzz'

/-- `G^{j+m}(w) = ∑_z (T^j)(w,z) * G^m(z)`. -/
theorem forwardWeight_add {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (j m : ℕ) (w : Vertex k) :
    forwardWeight k (j + m) K w
      = ∑ z : Vertex k, ((transitionMatrix k K) ^ j) w z * forwardWeight k m K z := by
  rw [forwardWeight_eq_pow htri (j + m) w, pow_add, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [forwardWeight_eq_pow htri m z]

/-! ## 3. The part of a path from the crossing onward -/

/-- `h_t(x)` restricted to states `x` above the level `q'`. -/
noncomputable def upperBackward (k q' t : ℕ)
    (K : Vertex k → Vertex k → ℝ) (x : Vertex k) : Poly k :=
  if q' < x.val then backwardWeight k t K x else 0

/-- From a state `w ≤ q'`: cross above `q'` at once, then `t` further jumps
    to `k`. Zero for `w > q'`. -/
noncomputable def suffixCore (k q' t : ℕ)
    (K : Vertex k → Vertex k → ℝ) (w : Vertex k) : Poly k :=
  if w.val ≤ q' then
    ∑ x : Vertex k, upperBackward k q' t K x * transitionMatrix k K x w
  else 0

/-- From a state `z`: `j` jumps, then cross above `q'`, then `t` further jumps
    to `k`. -/
noncomputable def suffixTail (k q' j t : ℕ)
    (K : Vertex k → Vertex k → ℝ) (z : Vertex k) : Poly k :=
  ∑ w : Vertex k, ((transitionMatrix k K) ^ j) w z * suffixCore k q' t K w

theorem coeffNonneg_upperBackward {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (q' t : ℕ) (x : Vertex k) : CoeffNonneg (upperBackward k q' t K x) := by
  unfold upperBackward
  split_ifs
  · exact coeffNonneg_backwardWeight htri hpos t x
  · exact coeffNonneg_zero

theorem coeffNonneg_suffixCore {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (q' t : ℕ) (w : Vertex k) : CoeffNonneg (suffixCore k q' t K w) := by
  unfold suffixCore
  split_ifs
  · exact coeffNonneg_sum _ _ (fun x _ =>
      coeffNonneg_mul (coeffNonneg_upperBackward htri hpos q' t x)
        (coeffNonneg_transitionMatrix htri hpos x w))
  · exact coeffNonneg_zero

theorem coeffNonneg_suffixTail {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (q' j t : ℕ) (z : Vertex k) : CoeffNonneg (suffixTail k q' j t K z) := by
  unfold suffixTail
  exact coeffNonneg_sum _ _ (fun w _ =>
    coeffNonneg_mul (coeffNonneg_pow_entry htri hpos j w z)
      (coeffNonneg_suffixCore htri hpos q' t w))

theorem suffixTail_zero (K : Vertex k → Vertex k → ℝ) (q' t : ℕ) (z : Vertex k) :
    suffixTail k q' 0 t K z = suffixCore k q' t K z := by
  unfold suffixTail
  rw [pow_zero, Fintype.sum_eq_single z]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro w hw
    rw [Matrix.one_apply_ne hw, zero_mul]

/-- Prepending one jump: `Tail_{j+1}(z) = ∑_v Tail_j(v) * T(v,z)`. -/
theorem suffixTail_succ (K : Vertex k → Vertex k → ℝ) (q' j t : ℕ) (z : Vertex k) :
    suffixTail k q' (j + 1) t K z
      = ∑ v : Vertex k, suffixTail k q' j t K v * transitionMatrix k K v z := by
  unfold suffixTail
  calc ∑ w : Vertex k, ((transitionMatrix k K) ^ (j + 1)) w z * suffixCore k q' t K w
      = ∑ w : Vertex k, ∑ v : Vertex k,
          ((transitionMatrix k K) ^ j) w v * transitionMatrix k K v z
            * suffixCore k q' t K w := by
        apply Finset.sum_congr rfl
        intro w _
        rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
    _ = ∑ v : Vertex k, ∑ w : Vertex k,
          ((transitionMatrix k K) ^ j) w v * transitionMatrix k K v z
            * suffixCore k q' t K w := Finset.sum_comm
    _ = ∑ v : Vertex k,
          (∑ w : Vertex k, ((transitionMatrix k K) ^ j) w v * suffixCore k q' t K w)
            * transitionMatrix k K v z := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        ring

/-- A tail started above the level `q'` is empty. -/
theorem suffixTail_eq_zero_of_gt {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (q' j t : ℕ) (z : Vertex k)
    (hz : q' < z.val) : suffixTail k q' j t K z = 0 := by
  unfold suffixTail
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : w.val ≤ q'
  · have hwz : w < z := by
      have h : w.val < z.val := by omega
      exact h
    rw [pow_entry_eq_zero_of_lt htri j w z hwz, zero_mul]
  · unfold suffixCore
    rw [ite_eq_right hw, mul_zero]

/-- `Tail` is coefficientwise TP2 in (number of visits after the crossing,
    start state), at a common total number of jumps `j + s = j' + s'`. -/
theorem suffixTail_minor {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : FullTP2 K) (q' : ℕ) (j' : ℕ) :
    ∀ j s s' : ℕ, s < s' → j + s = j' + s' → ∀ z z' : Vertex k, z < z' →
      CoeffNonneg
        (suffixTail k q' j s K z * suffixTail k q' j' s' K z'
          - suffixTail k q' j s K z' * suffixTail k q' j' s' K z) := by
  induction j' with
  | zero =>
    intro j s s' hs hsum z z' hzz'
    obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
    have hzz'v : z.val < z'.val := hzz'
    rw [suffixTail_zero K q' s' z', suffixTail_zero K q' s' z,
      suffixTail_succ K q' j0 s z, suffixTail_succ K q' j0 s z']
    by_cases hz' : z'.val ≤ q'
    · -- both start states are at or below the level: disjoint supports
      have hz : z.val ≤ q' := by omega
      unfold suffixCore
      rw [ite_eq_left hz', ite_eq_left hz]
      apply col_transport_full hK (fun v => suffixTail k q' j0 s K v)
        (fun x => upperBackward k q' s' K x) _ z z' hzz'
      intro v x hvx
      have hvxv : v.val < x.val := hvx
      have hzero : suffixTail k q' j0 s K x * upperBackward k q' s' K v = 0 := by
        by_cases hv : q' < v.val
        · rw [suffixTail_eq_zero_of_gt htri q' j0 s x (by omega), zero_mul]
        · unfold upperBackward
          rw [ite_eq_right hv, mul_zero]
      rw [hzero, sub_zero]
      exact coeffNonneg_mul (coeffNonneg_suffixTail htri hpos q' j0 s v)
        (coeffNonneg_upperBackward htri hpos q' s' x)
    · -- the larger start state is above the level: everything vanishes
      have h1 : suffixCore k q' s' K z' = 0 := by
        unfold suffixCore
        rw [ite_eq_right hz']
      have h2 : (∑ v : Vertex k, suffixTail k q' j0 s K v * transitionMatrix k K v z') = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        by_cases hv : v.val ≤ q'
        · have hvz : v ≤ z' := by
            have h : v.val ≤ z'.val := by omega
            exact h
          rw [transitionMatrix_eq_zero htri hvz, mul_zero]
        · rw [suffixTail_eq_zero_of_gt htri q' j0 s v (by omega), zero_mul]
      rw [h1, h2, mul_zero, zero_mul, sub_zero]
      exact coeffNonneg_zero
  | succ j' ih =>
    intro j s s' hs hsum z z' hzz'
    obtain ⟨j0, rfl⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
    rw [suffixTail_succ K q' j0 s z, suffixTail_succ K q' j' s' z',
      suffixTail_succ K q' j0 s z', suffixTail_succ K q' j' s' z]
    exact col_transport_full hK (fun v => suffixTail k q' j0 s K v)
      (fun v => suffixTail k q' j' s' K v)
      (fun v x hvx => ih j0 s s' hs (by omega) v x hvx) z z' hzz'

/-! ## 4. Common-time split from the end, and the theorem -/

/-- A path crossing above `q'` at jump `ρ + 1`, followed by `t` more jumps to
    `k`: `E^{ρ+1+t}_ρ(k) = ∑_w G^ρ(w) * Core_t(w)`. -/
theorem crossingWeight_eq_forward_core {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (q' ρ t : ℕ) :
    crossingWeight k (ρ + 1 + t) q' ρ K ⟨k, Nat.lt_succ_self k⟩
      = ∑ w : Vertex k, forwardWeight k ρ K w * suffixCore k q' t K w := by
  rw [crossingWeight_endpoint_split htri q' ρ (ρ + 1) (Nat.lt_succ_self ρ) t]
  calc ∑ z : Vertex k, crossingWeight k (ρ + 1) q' ρ K z * backwardWeight k t K z
      = ∑ z : Vertex k, ∑ w : Vertex k,
          cappedForward k ρ q' K w * (upperBackward k q' t K z * transitionMatrix k K z w) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [crossingWeight_succ_last htri ρ q' z]
        unfold upperBackward
        by_cases hz : q' < z.val
        · rw [ite_eq_left hz, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w _
          rw [ite_eq_left hz]
          have hT : transitionMatrix k K z w = stepWeight K z w := rfl
          rw [hT]
          ring
        · rw [ite_eq_right hz, zero_mul]
          symm
          apply Finset.sum_eq_zero
          intro w _
          rw [ite_eq_right hz, zero_mul, mul_zero]
    _ = ∑ w : Vertex k, ∑ z : Vertex k,
          cappedForward k ρ q' K w * (upperBackward k q' t K z * transitionMatrix k K z w) :=
        Finset.sum_comm
    _ = ∑ w : Vertex k, forwardWeight k ρ K w * suffixCore k q' t K w := by
        apply Finset.sum_congr rfl
        intro w _
        unfold cappedForward suffixCore
        by_cases hw : w.val ≤ q'
        · rw [ite_eq_left hw, ite_eq_left hw, Finset.mul_sum]
        · rw [ite_eq_right hw, ite_eq_right hw, mul_zero]
          apply Finset.sum_eq_zero
          intro z _
          rw [zero_mul]

/-- Split at the vertex `j + 1 + s` jumps before the end. -/
theorem suffix_split {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (q' j m s : ℕ) :
    crossingWeight k (j + m + 1 + s) q' (j + m) K ⟨k, Nat.lt_succ_self k⟩
      = ∑ z : Vertex k, forwardWeight k m K z * suffixTail k q' j s K z := by
  rw [crossingWeight_eq_forward_core htri q' (j + m) s]
  unfold suffixTail
  calc ∑ w : Vertex k, forwardWeight k (j + m) K w * suffixCore k q' s K w
      = ∑ w : Vertex k, ∑ z : Vertex k,
          ((transitionMatrix k K) ^ j) w z * forwardWeight k m K z
            * suffixCore k q' s K w := by
        apply Finset.sum_congr rfl
        intro w _
        rw [forwardWeight_add htri j m w, Finset.sum_mul]
    _ = ∑ z : Vertex k, ∑ w : Vertex k,
          ((transitionMatrix k K) ^ j) w z * forwardWeight k m K z
            * suffixCore k q' s K w := Finset.sum_comm
    _ = ∑ z : Vertex k, forwardWeight k m K z
          * ∑ w : Vertex k, ((transitionMatrix k K) ^ j) w z * suffixCore k q' s K w := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring

/-- Manuscript Theorem 3.10 (two-sided clause), in expanded-minor form. -/
theorem suffix_count_aux {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : FullTP2 K) (q : ℕ) (hq0 : 1 ≤ q) (hqk : q < k)
    (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg
      (suffixArray k q r s K * suffixArray k q r' s' K
        - suffixArray k q r s' K * suffixArray k q r' s K) := by
  by_cases hsr : s' ≤ r
  · have H : ∀ n σ j m : ℕ, σ ≤ n → j + m = n - σ →
        suffixArray k q n σ K
          = ∑ z : Vertex k, forwardWeight k m K z * suffixTail k (q - 1) j σ K z := by
      intro n σ j m hσ hjm
      rw [suffixArray_eq K q hq0 hqk n σ, ite_eq_left hσ]
      have e2 : n - σ = j + m := hjm.symm
      have e1 : n + 1 = j + m + 1 + σ := by omega
      rw [e2, e1]
      exact suffix_split htri (q - 1) j m σ
    rw [H r s (s' - s) (r - s') (by omega) (by omega),
      H r' s' 0 (r' - s') (by omega) (by omega),
      H r s' 0 (r - s') hsr (by omega),
      H r' s (s' - s) (r' - s') (by omega) (by omega)]
    apply doubled_sum_nonneg (fun z => forwardWeight k (r - s') K z)
      (fun z => forwardWeight k (r' - s') K z)
      (fun z => suffixTail k (q - 1) (s' - s) s K z)
      (fun z => suffixTail k (q - 1) 0 s' K z)
    intro z z' hzz'
    exact coeffNonneg_mul
      (forward_minor htri hpos hK (r - s') (r' - s') (by omega) z z' hzz')
      (suffixTail_minor htri hpos hK (q - 1) 0 (s' - s) s s' hs (by omega) z z' hzz')
  · -- `s' > r`: the entry `H(r,s')` is an empty sum
    have h0 : suffixArray k q r s' K = 0 := by
      rw [suffixArray_eq K q hq0 hqk r s', ite_eq_right hsr]
    rw [h0, zero_mul, sub_zero]
    exact coeffNonneg_mul (coeffNonneg_suffixArray htri hpos q r s)
      (coeffNonneg_suffixArray htri hpos q r' s')

end CommonTime
