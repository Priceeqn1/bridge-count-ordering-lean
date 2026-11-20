import CommonTime.Normalize

/-!
# Grouping by monomial: the combinatorial core (Theorem 4.7, step 4b/5)
-/

open scoped symmDiff

namespace CommonTime

/-- Number of elements in `[1, q]`. -/
def pcN (q : ℕ) (U : Finset ℕ) : ℕ := (U.filter (fun v => 0 < v ∧ v ≤ q)).card

/-! ## Multiplicity patterns -/

theorem cnt_eq_iff (U₁ U₂ P₁ P₂ : Finset ℕ) :
    cnt U₁ U₂ = cnt P₁ P₂ ↔ (U₁ ∩ U₂ = P₁ ∩ P₂ ∧ U₁ ∆ U₂ = P₁ ∆ P₂) := by
  constructor
  · intro h
    have hx : ∀ x, cnt U₁ U₂ x = cnt P₁ P₂ x := fun x => congrFun h x
    constructor <;> ext x <;> have := hx x <;>
      simp only [Finset.mem_inter, Finset.mem_symmDiff] <;> unfold cnt at this <;>
      by_cases a : x ∈ U₁ <;> by_cases b : x ∈ U₂ <;> by_cases c : x ∈ P₁ <;>
      by_cases d : x ∈ P₂ <;> simp_all
  · rintro ⟨h1, h2⟩
    funext x
    have e1 := Finset.ext_iff.mp h1 x
    have e2 := Finset.ext_iff.mp h2 x
    simp only [Finset.mem_inter, Finset.mem_symmDiff] at e1 e2
    unfold cnt
    by_cases a : x ∈ U₁ <;> by_cases b : x ∈ U₂ <;> by_cases c : x ∈ P₁ <;>
      by_cases d : x ∈ P₂ <;> simp_all

/-! ## The fibre of a multiplicity pattern -/

theorem T_disj_D (P₁ P₂ : Finset ℕ) : Disjoint (P₁ ∩ P₂) (P₁ ∆ P₂) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_inter, Finset.mem_symmDiff] at hx hx'
  tauto

theorem fibre_decomp (P₁ P₂ : Finset ℕ) {U₁ U₂ : Finset ℕ} (h : cnt U₁ U₂ = cnt P₁ P₂) :
    U₁ = (P₁ ∩ P₂) ∪ (U₁ \ U₂) ∧ U₂ = (P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ (U₁ \ U₂))
      ∧ U₁ \ U₂ ⊆ P₁ ∆ P₂ := by
  obtain ⟨h1, h2⟩ := (cnt_eq_iff U₁ U₂ P₁ P₂).mp h
  rw [← h1, ← h2]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_symmDiff]
    tauto
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at hx ⊢
    tauto

theorem fibre_inv (P₁ P₂ : Finset ℕ) {E : Finset ℕ} (hE : E ⊆ P₁ ∆ P₂) :
    cnt ((P₁ ∩ P₂) ∪ E) ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) = cnt P₁ P₂
      ∧ ((P₁ ∩ P₂) ∪ E) \ ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) = E := by
  have hd := T_disj_D P₁ P₂
  have hdx : ∀ x, x ∈ P₁ ∩ P₂ → x ∈ P₁ ∆ P₂ → False :=
    fun x h h' => Finset.disjoint_left.mp hd h h'
  refine ⟨?_, ?_⟩
  · rw [cnt_eq_iff]
    constructor
    · ext x
      have hEx := @hE x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_symmDiff] at hEx hdx ⊢
      have := hdx x
      tauto
    · ext x
      have hEx := @hE x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_symmDiff] at hEx hdx ⊢
      have := hdx x
      tauto
  · ext x
    have hEx := @hE x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_symmDiff] at hEx hdx ⊢
    have := hdx x
    tauto

/-! ## Arithmetic of the evaluation -/

theorem arith_eval {t N p Nm i j r r' s s' : ℕ} (hij : i + j ≤ N) (hi : i ≤ Nm) (w : ℝ) :
    (if (t + (i + j) = r' + 2 ∧ t + (N - (i + j)) = r + 2) then
        ((if (p + i = s' ∧ p + (Nm - i) = s) then (1 : ℝ) else 0)
          - (if (p + i = s ∧ p + (Nm - i) = s') then 1 else 0)) * w
      else 0)
    = if (2 * t + N = r + r' + 4 ∧ 2 * p + Nm = s + s') then
        ((if ((i : ℤ) = (s' : ℤ) - p ∧ (j : ℤ) = (r' : ℤ) + 2 - t - ((s' : ℤ) - p)) then w else 0)
          - (if ((i : ℤ) = (s : ℤ) - p ∧ (j : ℤ) = (r' : ℤ) + 2 - t - ((s : ℤ) - p))
              then w else 0))
      else 0 := by
  split_ifs <;> first | (exfalso; omega) | ring

/-! ## The summand and its evaluation on the fibre -/

/-- The summand of the grouped minor, for a pair of vertex sets of row types
    `r'` (first) and `r` (second). -/
noncomputable def Omega (ψ : ℝ) (k : ℕ) (pc : Finset ℕ → ℕ) (r r' s s' : ℕ)
    (U₁ U₂ : Finset ℕ) : ℝ :=
  if ((0 ∈ U₁ ∧ k ∈ U₁ ∧ 0 ∈ U₂ ∧ k ∈ U₂) ∧ (U₁.card = r' + 2 ∧ U₂.card = r + 2)) then
    ((if pc U₁ = s' ∧ pc U₂ = s then (1 : ℝ) else 0)
      - (if pc U₁ = s ∧ pc U₂ = s' then 1 else 0))
      * bondWeight ψ (U₁ ∆ U₂) (U₁ \ U₂)
  else 0

theorem pcN_union {q : ℕ} {A B : Finset ℕ} (h : Disjoint A B) :
    pcN q (A ∪ B) = pcN q A + pcN q B := by
  unfold pcN
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

theorem pcN_eq_card_inter {q : ℕ} {E D : Finset ℕ} (hE : E ⊆ D) (h0 : 0 ∉ D) :
    pcN q E = (E ∩ D.filter (fun v => v ≤ q)).card := by
  unfold pcN
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hx, _, hq⟩
    exact ⟨hx, hE hx, hq⟩
  · rintro ⟨hx, _, hq⟩
    refine ⟨hx, ?_, hq⟩
    rcases Nat.eq_zero_or_pos x with h | h
    · exact absurd (h ▸ hE hx) h0
    · exact h

theorem card_split {E D : Finset ℕ} (q : ℕ) (hE : E ⊆ D) :
    E.card = (E ∩ D.filter (fun v => v ≤ q)).card + (E ∩ D.filter (fun v => ¬ v ≤ q)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    constructor
    · intro hx
      by_cases h : x ≤ q
      · exact Or.inl ⟨hx, hE hx, h⟩
      · exact Or.inr ⟨hx, hE hx, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_inter, Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2

theorem Omega_eval (ψ : ℝ) (k q r r' s s' : ℕ) (P₁ P₂ : Finset ℕ)
    (h0 : 0 ∈ P₁ ∩ P₂) (hk : k ∈ P₁ ∩ P₂) {E : Finset ℕ} (hE : E ⊆ P₁ ∆ P₂) :
    Omega ψ k (pcN q) r r' s s' ((P₁ ∩ P₂) ∪ E) ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))
      = if (2 * (P₁ ∩ P₂).card + (P₁ ∆ P₂).card = r + r' + 4
            ∧ 2 * pcN q (P₁ ∩ P₂) + ((P₁ ∆ P₂).filter (fun v => v ≤ q)).card = s + s') then
          ((if ((E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card : ℤ) = (s' : ℤ) - pcN q (P₁ ∩ P₂)
              ∧ ((E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v ≤ q)).card : ℤ)
                  = (r' : ℤ) + 2 - (P₁ ∩ P₂).card - ((s' : ℤ) - pcN q (P₁ ∩ P₂))
            then bondWeight ψ (P₁ ∆ P₂) E else 0)
          - (if ((E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card : ℤ) = (s : ℤ) - pcN q (P₁ ∩ P₂)
              ∧ ((E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v ≤ q)).card : ℤ)
                  = (r' : ℤ) + 2 - (P₁ ∩ P₂).card - ((s : ℤ) - pcN q (P₁ ∩ P₂))
            then bondWeight ψ (P₁ ∆ P₂) E else 0))
        else 0 := by
  obtain ⟨hcnt, hdiff⟩ := fibre_inv P₁ P₂ hE
  have hsym := ((cnt_eq_iff _ _ P₁ P₂).mp hcnt).2
  have hd := T_disj_D P₁ P₂
  have hTE : Disjoint (P₁ ∩ P₂) E := Finset.disjoint_of_subset_right hE hd
  have hTDE : Disjoint (P₁ ∩ P₂) ((P₁ ∆ P₂) \ E) :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset hd
  have h0D : 0 ∉ P₁ ∆ P₂ := fun h => Finset.disjoint_left.mp hd h0 h
  have hc1 : ((P₁ ∩ P₂) ∪ E).card = (P₁ ∩ P₂).card + E.card :=
    Finset.card_union_of_disjoint hTE
  have hc2 : ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)).card
      = (P₁ ∩ P₂).card + ((P₁ ∆ P₂) \ E).card := Finset.card_union_of_disjoint hTDE
  have hsd := Finset.card_sdiff_add_card_eq_card hE
  have hp1 : pcN q ((P₁ ∩ P₂) ∪ E) = pcN q (P₁ ∩ P₂) + pcN q E := pcN_union hTE
  have hp2 : pcN q ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))
      = pcN q (P₁ ∩ P₂) + pcN q ((P₁ ∆ P₂) \ E) := pcN_union hTDE
  have hpD : pcN q (P₁ ∆ P₂) = pcN q ((P₁ ∆ P₂) \ E) + pcN q E := by
    rw [← pcN_union (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset hE]
  have hpE := pcN_eq_card_inter (q := q) hE h0D
  have hpDD := pcN_eq_card_inter (q := q) (Finset.Subset.refl (P₁ ∆ P₂)) h0D
  have hEc := card_split q hE
  have hDm : ((P₁ ∆ P₂) ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)) = (P₁ ∆ P₂).filter (fun v => v ≤ q) :=
    Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  rw [hDm] at hpDD
  have hij : (E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card
      + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v ≤ q)).card ≤ (P₁ ∆ P₂).card := by
    rw [← hEc]
    exact Finset.card_le_card hE
  have hi : (E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card
      ≤ ((P₁ ∆ P₂).filter (fun v => v ≤ q)).card :=
    Finset.card_le_card Finset.inter_subset_right
  have m1 : (0 ∈ (P₁ ∩ P₂) ∪ E) := Finset.mem_union_left _ h0
  have m2 : (k ∈ (P₁ ∩ P₂) ∪ E) := Finset.mem_union_left _ hk
  have m3 : (0 ∈ (P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) := Finset.mem_union_left _ h0
  have m4 : (k ∈ (P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) := Finset.mem_union_left _ hk
  unfold Omega
  rw [hsym, hdiff]
  simp only [m1, m2, m3, m4, and_self, true_and]
  have e1 : ((P₁ ∩ P₂) ∪ E).card
      = (P₁ ∩ P₂).card + ((E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card
          + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v ≤ q)).card) := by
    rw [hc1, ← hEc]
  have e2 : ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)).card
      = (P₁ ∩ P₂).card + ((P₁ ∆ P₂).card - ((E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card
          + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v ≤ q)).card)) := by
    rw [hc2, ← hEc]
    omega
  have e3 : pcN q ((P₁ ∩ P₂) ∪ E)
      = pcN q (P₁ ∩ P₂) + (E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card := by
    rw [hp1, hpE]
  have e4 : pcN q ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))
      = pcN q (P₁ ∩ P₂) + (((P₁ ∆ P₂).filter (fun v => v ≤ q)).card
          - (E ∩ (P₁ ∆ P₂).filter (fun v => v ≤ q)).card) := by
    rw [hp2]
    omega
  rw [e1, e2, e3, e4]
  exact arith_eval hij hi _

/-! ## The weight sums `Z(i, j)` -/

theorem Zsum_nonneg {ψ : ℝ} (hψ : 0 ≤ ψ) (Dm Dp : Finset ℕ) (i j : ℤ) :
    0 ≤ Zsum ψ Dm Dp i j := by
  unfold Zsum
  apply Finset.sum_nonneg
  intro E _
  split_ifs
  · rw [bondWeight_eq_pow]
    exact pow_nonneg hψ _
  · exact le_refl 0

theorem Zsum_zero_of_out (ψ : ℝ) (Dm Dp : Finset ℕ) {i j : ℤ}
    (h : i < 0 ∨ (Dm.card : ℤ) < i ∨ j < 0 ∨ (Dp.card : ℤ) < j) :
    Zsum ψ Dm Dp i j = 0 := by
  unfold Zsum
  apply Finset.sum_eq_zero
  intro E _
  apply ite_eq_right
  rintro ⟨h1, h2⟩
  have c1 : (E ∩ Dm).card ≤ Dm.card := Finset.card_le_card Finset.inter_subset_right
  have c2 : (E ∩ Dp).card ≤ Dp.card := Finset.card_le_card Finset.inter_subset_right
  omega

/-- **Cut-difference inequality for `Z`.** -/
theorem Zsum_diff_nonneg {ψ : ℝ} (hψ1 : 1 ≤ ψ) (hψ2 : ψ ≤ 2) {Dm Dp : Finset ℕ}
    (hDD : ∀ x ∈ Dm, ∀ y ∈ Dp, x < y) {ip im jp jm : ℤ}
    (hsum : ip + im = Dm.card) (hi : im < ip) (hj : jp < jm)
    (hjs : (Dp.card : ℤ) + 1 ≤ jp + jm) :
    Zsum ψ Dm Dp im jm ≤ Zsum ψ Dm Dp ip jp := by
  have hψ0 : 0 ≤ ψ := le_trans zero_le_one hψ1
  by_cases h1 : im < 0
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inl h1), Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inl (by omega)))]
  by_cases h2 : jp < 0
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inl h2))),
      Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inr (by omega))))]
  by_cases h3 : (Dp.card : ℤ) < jp
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inr h3))),
      Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inr (by omega))))]
  by_cases h4 : (Dp.card : ℤ) < jm
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inr h4)))]
    exact Zsum_nonneg hψ0 _ _ _ _
  -- the remaining case (30)
  have hDm : Dm.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hDp : Dp.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hA := enum_isChain_max hψ1 hψ2 Dm hDm
  have hB := enum_isChain_min hψ1 hψ2 Dp hDp
  have hκ : 1 ≤ (if Dm.max' hDm + 1 = Dp.min' hDp then ψ else 1) := by
    split_ifs
    · exact hψ1
    · exact le_refl 1
  have key := Zdiff_nonneg_isChain hA hB hκ ip jp jm (by omega) hj (by omega)
  have e : (Dm.card : ℤ) - ip = im := by omega
  rw [e] at key
  rw [Zsum_eq_Zpair ψ hDm hDp hDD, Zsum_eq_Zpair ψ hDm hDp hDD]
  exact key

/-! ## The core inequality -/

theorem Zsum_eq_sum_D (ψ : ℝ) {Dm Dp D : Finset ℕ} (hU : Dm ∪ Dp = D) (i j : ℤ) :
    Zsum ψ Dm Dp i j
      = ∑ E ∈ D.powerset,
          if ((E ∩ Dm).card : ℤ) = i ∧ ((E ∩ Dp).card : ℤ) = j
            then bondWeight ψ D E else 0 := by
  unfold Zsum
  rw [hU]

open Classical in
theorem core_nonneg {ψ : ℝ} (hψ1 : 1 ≤ ψ) (hψ2 : ψ ≤ 2) (k q r r' s s' : ℕ)
    (hr : r < r') (hs : s < s') (c : ℕ → ℕ) :
    0 ≤ ∑ U₁ ∈ (Finset.range (k + 1)).powerset, ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
      if cnt U₁ U₂ = c then Omega ψ k (pcN q) r r' s s' U₁ U₂ else 0 := by
  classical
  by_cases hex : ∃ P₁ ∈ (Finset.range (k + 1)).powerset, ∃ P₂ ∈ (Finset.range (k + 1)).powerset,
      cnt P₁ P₂ = c ∧ (0 ∈ P₁ ∧ k ∈ P₁ ∧ 0 ∈ P₂ ∧ k ∈ P₂)
  swap
  · apply le_of_eq
    symm
    apply Finset.sum_eq_zero
    intro U₁ hU₁
    apply Finset.sum_eq_zero
    intro U₂ hU₂
    by_cases hc : cnt U₁ U₂ = c
    · rw [ite_eq_left hc]
      unfold Omega
      apply ite_eq_right
      rintro ⟨hm, _⟩
      exact absurd ⟨U₁, hU₁, U₂, hU₂, hc, hm⟩ hex
    · rw [ite_eq_right hc]
  obtain ⟨P₁, hP₁, P₂, hP₂, hc, hm⟩ := hex
  subst hc
  obtain ⟨m1, m2, m3, m4⟩ := hm
  have h0 : 0 ∈ P₁ ∩ P₂ := Finset.mem_inter.mpr ⟨m1, m3⟩
  have hk : k ∈ P₁ ∩ P₂ := Finset.mem_inter.mpr ⟨m2, m4⟩
  rw [Finset.mem_powerset] at hP₁ hP₂
  have hRange : ∀ E, E ⊆ P₁ ∆ P₂ → (P₁ ∩ P₂) ∪ E ⊆ Finset.range (k + 1) := by
    intro E hE x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hP₁ (Finset.mem_inter.mp hx).1
    · have := hE hx
      rw [Finset.mem_symmDiff] at this
      rcases this with h | h
      · exact hP₁ h.1
      · exact hP₂ h.1
  have hbij : ∑ U₁ ∈ (Finset.range (k + 1)).powerset, ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
      (if cnt U₁ U₂ = cnt P₁ P₂ then Omega ψ k (pcN q) r r' s s' U₁ U₂ else 0)
      = ∑ E ∈ (P₁ ∆ P₂).powerset,
          Omega ψ k (pcN q) r r' s s' ((P₁ ∩ P₂) ∪ E) ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) := by
    rw [← Finset.sum_product' (Finset.range (k + 1)).powerset (Finset.range (k + 1)).powerset
      (fun U₁ U₂ => if cnt U₁ U₂ = cnt P₁ P₂ then Omega ψ k (pcN q) r r' s s' U₁ U₂ else 0),
      ← Finset.sum_filter]
    refine Finset.sum_bij' (fun p _ => p.1 \ p.2)
      (fun E _ => ((P₁ ∩ P₂) ∪ E, (P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_powerset]
      exact (fibre_decomp P₁ P₂ hp.2).2.2
    · intro E hE
      rw [Finset.mem_powerset] at hE
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
      refine ⟨⟨hRange E hE, ?_⟩, (fibre_inv P₁ P₂ hE).1⟩
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hP₁ (Finset.mem_inter.mp hx).1
      · have := Finset.sdiff_subset hx
        rw [Finset.mem_symmDiff] at this
        rcases this with h | h
        · exact hP₁ h.1
        · exact hP₂ h.1
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨d1, d2, _⟩ := fibre_decomp P₁ P₂ hp.2
      exact Prod.ext d1.symm d2.symm
    · intro E hE
      rw [Finset.mem_powerset] at hE
      exact (fibre_inv P₁ P₂ hE).2
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨d1, d2, _⟩ := fibre_decomp P₁ P₂ hp.2
      show Omega ψ k (pcN q) r r' s s' p.1 p.2 = Omega ψ k (pcN q) r r' s s' _ _
      rw [← d1, ← d2]
  rw [hbij]
  -- evaluate every term
  rw [Finset.sum_congr rfl (fun E hE => Omega_eval ψ k q r r' s s' P₁ P₂ h0 hk
    (Finset.mem_powerset.mp hE))]
  set T := P₁ ∩ P₂ with hT
  set D := P₁ ∆ P₂ with hD
  set Dm := D.filter (fun v => v ≤ q) with hDm
  set Dp := D.filter (fun v => ¬ v ≤ q) with hDp
  have hU : Dm ∪ Dp = D := by
    ext x
    simp only [hDm, hDp, Finset.mem_union, Finset.mem_filter]
    tauto
  have hND : D.card = Dm.card + Dp.card := by
    have := card_split q (Finset.Subset.refl D)
    rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)] at this
    exact this
  have hDD : ∀ x ∈ Dm, ∀ y ∈ Dp, x < y := by
    intro x hx y hy
    rw [hDm, Finset.mem_filter] at hx
    rw [hDp, Finset.mem_filter] at hy
    omega
  by_cases hQ : (2 * T.card + D.card = r + r' + 4 ∧ 2 * pcN q T + Dm.card = s + s')
  · simp only [hQ, and_self, ↓reduceIte]
    rw [Finset.sum_sub_distrib]
    have z1 := Zsum_eq_sum_D ψ hU ((s' : ℤ) - pcN q T)
      ((r' : ℤ) + 2 - T.card - ((s' : ℤ) - pcN q T))
    have z2 := Zsum_eq_sum_D ψ hU ((s : ℤ) - pcN q T)
      ((r' : ℤ) + 2 - T.card - ((s : ℤ) - pcN q T))
    rw [← z1, ← z2, sub_nonneg]
    obtain ⟨hQ1, hQ2⟩ := hQ
    exact Zsum_diff_nonneg hψ1 hψ2 hDD (by omega) (by omega) (by omega) (by omega)
  · simp only [hQ, ↓reduceIte]
    simp

end CommonTime