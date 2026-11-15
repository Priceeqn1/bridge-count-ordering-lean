import CommonTime.Crossing

/-!
# Prefix count arrays (manuscript Theorem 3.10, positive-column prefix part)

`prefixArray k q r s K` is the total weight of increasing paths `0 → k` with
`r` intermediate vertices, exactly `s` of which lie in `[1, q]`. This file
proves that its ordered `2 × 2` minors are coefficientwise nonnegative:

  `H(r,s) * H(r',s') - H(r,s') * H(r',s) ⪰ 0` for `r < r'`, `s < s'`,

under strict lower-triangularity, positivity on admissible edges,
positive-column TP2 and `q < k`.

Structure:
1. admissible paths are strictly monotone; an admissible path `0 → k` with
   `q < k` crosses above `q` at exactly one jump, and the number of its
   intermediate vertices `≤ q` is the index of that jump
   (`prefixVisits_eq_iff_crossesAt`);
2. hence `prefixArray k q r s K = crossingWeight k (r+1) q s K k`
   (`prefixArray_eq_crossingWeight`);
3. common-time split: a path that has crossed within its first `ϑ` jumps
   factors through its vertex at time `ϑ` (`crossingWeight_split`);
4. the theorem, by splitting all four path families at the common time
   `ϑ = s' + 1` and combining the crossing-time lemma (in the state variable
   at time `ϑ`) with the backward time/state lemma, through the doubled
   Cauchy--Binet identity.

Nothing here evaluates the activities at numbers and nothing bounds `k`.
-/

namespace CommonTime

variable {k : ℕ}

/-! ## 1. Monotone paths, the unique crossing, and the visit count -/

theorem admissibleTo_strictMono {m : ℕ} {z : Vertex k} {p : Path k m}
    (h : admissibleTo k m z p) : StrictMono p :=
  Fin.strictMono_iff_lt_succ.mpr h.2.2

/-- Discrete intermediate value statement on `ℕ`. -/
theorem nat_exists_crossing (f : ℕ → ℕ) (q : ℕ) (h0 : f 0 ≤ q) :
    ∀ m : ℕ, q < f m → ∃ ρ, ρ < m ∧ f ρ ≤ q ∧ q < f (ρ + 1) := by
  intro m
  induction m with
  | zero =>
    intro h
    omega
  | succ m ih =>
    intro h
    by_cases hm : q < f m
    · obtain ⟨ρ, hρ, h1, h2⟩ := ih hm
      exact ⟨ρ, Nat.lt_succ_of_lt hρ, h1, h2⟩
    · exact ⟨m, Nat.lt_succ_self m, Nat.le_of_not_lt hm, h⟩

/-- An admissible path from `0` to a state above `q` crosses above `q`. -/
theorem exists_crossesAt {m : ℕ} {z : Vertex k} {p : Path k m} (q : ℕ)
    (h : admissibleTo k m z p) (hqz : q < z.val) :
    ∃ ρ, crossesAt k m q ρ p := by
  have h0 : (p ⟨min 0 m, by omega⟩).val ≤ q := by
    have e : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ m⟩ :=
      Fin.ext (by show min 0 m = 0; omega)
    rw [e, h.1]
    exact Nat.zero_le q
  have hm : q < (p ⟨min m m, by omega⟩).val := by
    have e : (⟨min m m, by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
      Fin.ext (by show min m m = m; omega)
    rw [e, h.2.1]
    exact hqz
  obtain ⟨ρ, hρ, h1, h2⟩ :=
    nat_exists_crossing (fun i => (p ⟨min i m, by omega⟩).val) q h0 m hm
  have e1 : (⟨min ρ m, by omega⟩ : Fin (m + 1)) = ⟨ρ, Nat.lt_succ_of_lt hρ⟩ :=
    Fin.ext (by show min ρ m = ρ; omega)
  have e2 : (⟨min (ρ + 1) m, by omega⟩ : Fin (m + 1)) = ⟨ρ + 1, Nat.succ_lt_succ hρ⟩ :=
    Fin.ext (by show min (ρ + 1) m = ρ + 1; omega)
  have h1' : (p ⟨min ρ m, by omega⟩).val ≤ q := h1
  have h2' : q < (p ⟨min (ρ + 1) m, by omega⟩).val := h2
  rw [e1] at h1'
  rw [e2] at h2'
  exact ⟨ρ, hρ, h1', h2'⟩

/-- The number of positive indices `i ≤ ρ` in `Fin (m+1)`, for `ρ < m`. -/
theorem card_pos_le {m ρ : ℕ} (hρ : ρ < m) :
    (Finset.univ.filter (fun i : Fin (m + 1) => 0 < i.val ∧ i.val ≤ ρ)).card = ρ := by
  have hmap : (Finset.univ.filter (fun i : Fin (m + 1) => 0 < i.val ∧ i.val ≤ ρ)).map
      Fin.valEmbedding = Finset.Ioc 0 ρ := by
    ext j
    rw [Finset.mem_map, Finset.mem_Ioc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hj
      exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ioc, Nat.sub_zero]

/-- A strictly monotone path that crosses above `q` at jump `ρ + 1` has exactly
    `ρ` intermediate vertices `≤ q`. -/
theorem prefixVisits_eq_of_crossesAt {m : ℕ} {p : Path k m} (q ρ : ℕ)
    (hmono : StrictMono p) (hc : crossesAt k m q ρ p) :
    prefixVisits k m q p = ρ := by
  obtain ⟨hρ, h1, h2⟩ := hc
  have hS : ∀ i : Fin (m + 1),
      (0 < i.val ∧ i.val < m ∧ (p i).val ≤ q) ↔ (0 < i.val ∧ i.val ≤ ρ) := by
    intro i
    constructor
    · rintro ⟨hi0, _, hiq⟩
      refine ⟨hi0, ?_⟩
      by_contra hcon
      have hle : (⟨ρ + 1, Nat.succ_lt_succ hρ⟩ : Fin (m + 1)) ≤ i :=
        Fin.le_def.mpr (by show ρ + 1 ≤ i.val; omega)
      have hp : (p ⟨ρ + 1, Nat.succ_lt_succ hρ⟩).val ≤ (p i).val :=
        Fin.le_def.mp (hmono.monotone hle)
      omega
    · rintro ⟨hi0, hiρ⟩
      have hle : i ≤ (⟨ρ, Nat.lt_succ_of_lt hρ⟩ : Fin (m + 1)) :=
        Fin.le_def.mpr (by show i.val ≤ ρ; omega)
      have hp : (p i).val ≤ (p ⟨ρ, Nat.lt_succ_of_lt hρ⟩).val :=
        Fin.le_def.mp (hmono.monotone hle)
      exact ⟨hi0, by omega, by omega⟩
  unfold prefixVisits
  rw [Finset.filter_congr (fun i _ => hS i)]
  exact card_pos_le hρ

/-- For an admissible path to a state above `q`: it has exactly `s`
    intermediate vertices `≤ q` iff it crosses above `q` at jump `s + 1`. -/
theorem prefixVisits_eq_iff_crossesAt {m : ℕ} {z : Vertex k} {p : Path k m}
    (q s : ℕ) (h : admissibleTo k m z p) (hqz : q < z.val) :
    prefixVisits k m q p = s ↔ crossesAt k m q s p := by
  have hmono := admissibleTo_strictMono h
  constructor
  · intro hs
    obtain ⟨ρ, hρ⟩ := exists_crossesAt q h hqz
    have e : prefixVisits k m q p = ρ := prefixVisits_eq_of_crossesAt q ρ hmono hρ
    have hsρ : s = ρ := hs.symm.trans e
    rw [hsρ]
    exact hρ
  · exact prefixVisits_eq_of_crossesAt q s hmono

/-! ## 2. Prefix arrays are crossing weights at the endpoint `k` -/

theorem paths_eq_pathsTo (k m : ℕ) :
    paths k m = pathsTo k m ⟨k, Nat.lt_succ_self k⟩ := rfl

theorem prefixArray_eq_crossingWeight (K : Vertex k → Vertex k → ℝ)
    (q : ℕ) (hqk : q < k) (r s : ℕ) :
    prefixArray k q r s K
      = crossingWeight k (r + 1) q s K ⟨k, Nat.lt_succ_self k⟩ := by
  classical
  unfold prefixArray crossingWeight
  rw [paths_eq_pathsTo]
  apply Finset.sum_congr rfl
  intro p hp
  have hadm : admissibleTo k (r + 1) ⟨k, Nat.lt_succ_self k⟩ p := by
    unfold pathsTo at hp
    exact (Finset.mem_filter.mp hp).2
  have hiff := prefixVisits_eq_iff_crossesAt (p := p) q s hadm hqk
  by_cases hc : crossesAt k (r + 1) q s p
  · rw [ite_eq_left hc, ite_eq_left (hiff.mpr hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mp h))]

/-! ## 3. Common-time split -/

/-- No crossing can be indexed at or beyond the number of jumps. -/
theorem crossingWeight_eq_zero_of_ge (K : Vertex k → Vertex k → ℝ)
    (m q rho : ℕ) (h : m ≤ rho) (z : Vertex k) :
    crossingWeight k m q rho K z = 0 := by
  classical
  unfold crossingWeight
  apply Finset.sum_eq_zero
  intro p _
  apply ite_eq_right
  rintro ⟨hlt, _⟩
  omega

/-- A path that crosses above `q` within its first `ϑ` jumps factors through
    its vertex at time `ϑ`:
    `E^{ϑ+t}_ρ(y) = ∑_z E^ϑ_ρ(z) * (T^t)(y,z)` for `ρ < ϑ`. -/
theorem crossingWeight_split {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (q ρ ϑ : ℕ) (hρ : ρ < ϑ) (t : ℕ) :
    ∀ y : Vertex k,
      crossingWeight k (ϑ + t) q ρ K y
        = ∑ z : Vertex k, crossingWeight k ϑ q ρ K z
            * ((transitionMatrix k K) ^ t) y z := by
  induction t with
  | zero =>
    intro y
    rw [pow_zero, Fintype.sum_eq_single y]
    · rw [Matrix.one_apply_eq, mul_one]
      rfl
    · intro z hz
      rw [Matrix.one_apply_ne (fun h => hz h.symm), mul_zero]
  | succ t ih =>
    intro y
    have e : crossingWeight k (ϑ + (t + 1)) q ρ K y
        = ∑ w : Vertex k, crossingWeight k (ϑ + t) q ρ K w * stepWeight K y w :=
      crossingWeight_succ_lt htri q ρ (Nat.lt_of_lt_of_le hρ (Nat.le_add_right ϑ t)) y
    rw [e, pow_succ']
    calc ∑ w : Vertex k, crossingWeight k (ϑ + t) q ρ K w * stepWeight K y w
        = ∑ w : Vertex k, ∑ z : Vertex k,
            crossingWeight k ϑ q ρ K z * ((transitionMatrix k K) ^ t) w z
              * stepWeight K y w := by
          apply Finset.sum_congr rfl
          intro w _
          rw [ih w, Finset.sum_mul]
      _ = ∑ z : Vertex k, ∑ w : Vertex k,
            crossingWeight k ϑ q ρ K z * ((transitionMatrix k K) ^ t) w z
              * stepWeight K y w := Finset.sum_comm
      _ = ∑ z : Vertex k, crossingWeight k ϑ q ρ K z
            * (transitionMatrix k K * (transitionMatrix k K) ^ t) y z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          have hT : transitionMatrix k K y w = stepWeight K y w := rfl
          rw [hT]
          ring

/-- Endpoint form of the split, with the backward polynomials `h_t(z)`. -/
theorem crossingWeight_endpoint_split {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (q ρ ϑ : ℕ) (hρ : ρ < ϑ) (t : ℕ) :
    crossingWeight k (ϑ + t) q ρ K ⟨k, Nat.lt_succ_self k⟩
      = ∑ z : Vertex k, crossingWeight k ϑ q ρ K z * backwardWeight k t K z :=
  crossingWeight_split htri q ρ ϑ hρ t ⟨k, Nat.lt_succ_self k⟩

/-! ## 4. The prefix count-array theorem -/

/-- One ordered term of the Cauchy--Binet expansion at the common time. -/
theorem prefix_term_nonneg {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K) (q s s' t t' : ℕ) (hs : s < s') (ht : t < t')
    (z z' : Vertex k) (hzz' : z < z') :
    CoeffNonneg
      ((crossingWeight k (s' + 1) q s K z * crossingWeight k (s' + 1) q s' K z'
          - crossingWeight k (s' + 1) q s K z' * crossingWeight k (s' + 1) q s' K z)
        * (backwardWeight k t K z * backwardWeight k t' K z'
          - backwardWeight k t K z' * backwardWeight k t' K z)) := by
  by_cases hqz : q < z.val
  · have hE := crossing_minor_aux htri hpos hK q (s' + 1) s s' hs (Nat.lt_succ_self s')
      z z' hqz hzz'
    have hH := backward_minor_aux htri hpos hK t t' ht z z' (by omega) hzz'
    have e :
        (crossingWeight k (s' + 1) q s K z * crossingWeight k (s' + 1) q s' K z'
            - crossingWeight k (s' + 1) q s K z' * crossingWeight k (s' + 1) q s' K z)
          * (backwardWeight k t K z * backwardWeight k t' K z'
            - backwardWeight k t K z' * backwardWeight k t' K z)
        = (crossingWeight k (s' + 1) q s K z' * crossingWeight k (s' + 1) q s' K z
            - crossingWeight k (s' + 1) q s K z * crossingWeight k (s' + 1) q s' K z')
          * (backwardWeight k t K z' * backwardWeight k t' K z
            - backwardWeight k t K z * backwardWeight k t' K z') := by
      ring
    rw [e]
    exact coeffNonneg_mul hE hH
  · rw [crossingWeight_eq_zero_of_le htri q (s' + 1) s z (by omega) (by omega),
      crossingWeight_eq_zero_of_le htri q (s' + 1) s' z (Nat.lt_succ_self s') (by omega),
      zero_mul, mul_zero, sub_zero, zero_mul]
    exact coeffNonneg_zero

/-- Manuscript Theorem 3.10 (prefix part), in expanded-minor form. -/
theorem prefix_count_aux {K : Vertex k → Vertex k → ℝ}
    (htri : StrictLowerTriangular K) (hpos : PositiveAdmissible K)
    (hK : PositiveColumnTP2 K) (q : ℕ) (hqk : q < k)
    (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg
      (prefixArray k q r s K * prefixArray k q r' s' K
        - prefixArray k q r s' K * prefixArray k q r' s K) := by
  rw [prefixArray_eq_crossingWeight K q hqk r s, prefixArray_eq_crossingWeight K q hqk r' s',
    prefixArray_eq_crossingWeight K q hqk r s', prefixArray_eq_crossingWeight K q hqk r' s]
  by_cases hsr : s' ≤ r
  · -- split all four families at the common time `s' + 1`
    have H : ∀ n ρ : ℕ, ρ < s' + 1 → s' ≤ n →
        crossingWeight k (n + 1) q ρ K ⟨k, Nat.lt_succ_self k⟩
          = ∑ z : Vertex k, crossingWeight k (s' + 1) q ρ K z
              * backwardWeight k (n - s') K z := by
      intro n ρ hρ hn
      have e : n + 1 = (s' + 1) + (n - s') := by omega
      rw [e]
      exact crossingWeight_endpoint_split htri q ρ (s' + 1) hρ (n - s')
    rw [H r s (by omega) hsr, H r' s' (Nat.lt_succ_self s') (by omega),
      H r s' (Nat.lt_succ_self s') hsr, H r' s (by omega) (by omega)]
    rw [mul_comm (∑ z : Vertex k, crossingWeight k (s' + 1) q s' K z
        * backwardWeight k (r - s') K z)]
    apply coeffNonneg_of_add_self
    rw [cauchy_binet_doubled (fun z => crossingWeight k (s' + 1) q s K z)
      (fun z => crossingWeight k (s' + 1) q s' K z)
      (fun z => backwardWeight k (r - s') K z)
      (fun z => backwardWeight k (r' - s') K z)]
    apply coeffNonneg_sum
    intro z _
    apply coeffNonneg_sum
    intro z' _
    rcases lt_trichotomy z z' with hlt | heq | hgt
    · exact prefix_term_nonneg htri hpos hK q s s' (r - s') (r' - s') hs (by omega) z z' hlt
    · subst heq
      rw [sub_self, zero_mul]
      exact coeffNonneg_zero
    · have hterm := prefix_term_nonneg htri hpos hK q s s' (r - s') (r' - s') hs
        (by omega) z' z hgt
      have e :
          (crossingWeight k (s' + 1) q s K z * crossingWeight k (s' + 1) q s' K z'
              - crossingWeight k (s' + 1) q s K z' * crossingWeight k (s' + 1) q s' K z)
            * (backwardWeight k (r - s') K z * backwardWeight k (r' - s') K z'
              - backwardWeight k (r - s') K z' * backwardWeight k (r' - s') K z)
          = (crossingWeight k (s' + 1) q s K z' * crossingWeight k (s' + 1) q s' K z
              - crossingWeight k (s' + 1) q s K z * crossingWeight k (s' + 1) q s' K z')
            * (backwardWeight k (r - s') K z' * backwardWeight k (r' - s') K z
              - backwardWeight k (r - s') K z * backwardWeight k (r' - s') K z') := by
        ring
      rw [e]
      exact hterm
  · -- `s' > r`: the entry `H(r,s')` is an empty sum
    rw [crossingWeight_eq_zero_of_ge K (r + 1) q s' (by omega), zero_mul, sub_zero]
    exact coeffNonneg_mul (coeffNonneg_crossingWeight htri hpos (r + 1) q s _)
      (coeffNonneg_crossingWeight htri hpos (r' + 1) q s' _)

end CommonTime
