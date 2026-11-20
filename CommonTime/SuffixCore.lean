import CommonTime.Grouping

/-!
# The suffix clause: combinatorial core (Theorem 4.7(b))

For a suffix interval the counted vertices are those in `[q, k - 1]`, the upper
side of the cut. The roles of the two chains are exchanged: `Zpair` is
symmetric under swapping both chains and both indices, so the cut-difference
inequality applies with the chain of `D₊` as the left chain.
-/

open scoped symmDiff

namespace CommonTime

variable {k : ℕ}

theorem Zpair_comm (κ : ℝ) (A B : ChainState) (i j : ℤ) :
    Zpair κ A B i j = Zpair κ B A j i := by
  unfold Zpair
  ring

/-- Cut-difference inequality with the counted index on the upper side. -/
theorem Zsum_diff_nonneg_swap {ψ : ℝ} (hψ1 : 1 ≤ ψ) (hψ2 : ψ ≤ 2) {Dm Dp : Finset ℕ}
    (hDD : ∀ x ∈ Dm, ∀ y ∈ Dp, x < y) {ip im jp jm : ℤ}
    (hsum : jp + jm = Dp.card) (hj : jm < jp) (hi : ip < im)
    (his : (Dm.card : ℤ) + 1 ≤ ip + im) :
    Zsum ψ Dm Dp im jm ≤ Zsum ψ Dm Dp ip jp := by
  have hψ0 : 0 ≤ ψ := le_trans zero_le_one hψ1
  by_cases h1 : jm < 0
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inl h1))),
      Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inr (Or.inr (by omega))))]
  by_cases h2 : ip < 0
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inl h2),
      Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inl (by omega)))]
  by_cases h3 : (Dm.card : ℤ) < ip
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inl h3)),
      Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inl (by omega)))]
  by_cases h4 : (Dm.card : ℤ) < im
  · rw [Zsum_zero_of_out ψ Dm Dp (Or.inr (Or.inl h4))]
    exact Zsum_nonneg hψ0 _ _ _ _
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
  have key := Zdiff_nonneg_isChain hB hA hκ jp ip im (by omega) hi (by omega)
  have e : (Dp.card : ℤ) - jp = jm := by omega
  rw [e] at key
  rw [Zsum_eq_Zpair ψ hDm hDp hDD, Zsum_eq_Zpair ψ hDm hDp hDD,
    Zpair_comm _ _ _ im jm, Zpair_comm _ _ _ ip jp]
  exact key

/-! ## The suffix count -/

/-- Number of elements in `[q, k - 1]` that are interior vertices. -/
def sufN (q k : ℕ) (U : Finset ℕ) : ℕ := (U.filter (fun v => 0 < v ∧ v < k ∧ q ≤ v)).card

theorem sufN_union {q k : ℕ} {A B : Finset ℕ} (h : Disjoint A B) :
    sufN q k (A ∪ B) = sufN q k A + sufN q k B := by
  unfold sufN
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

theorem sufN_eq_card_inter {q k : ℕ} {E D : Finset ℕ} (hE : E ⊆ D)
    (hD : D ⊆ Finset.range (k + 1)) (h0 : 0 ∉ D) (hk : k ∉ D) :
    sufN q k E = (E ∩ D.filter (fun v => ¬ v < q)).card := by
  unfold sufN
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hx, _, _, hq⟩
    exact ⟨hx, hE hx, by omega⟩
  · rintro ⟨hx, hxD, hq⟩
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxD)
    have hxk : x ≠ k := fun h => hk (h ▸ hxD)
    have hxr := Finset.mem_range.mp (hD hxD)
    exact ⟨hx, by omega, by omega, by omega⟩

theorem card_split2 {E D : Finset ℕ} (P : ℕ → Prop) [DecidablePred P] (hE : E ⊆ D) :
    E.card = (E ∩ D.filter P).card + (E ∩ D.filter (fun v => ¬ P v)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    constructor
    · intro hx
      by_cases h : P x
      · exact Or.inl ⟨hx, hE hx, h⟩
      · exact Or.inr ⟨hx, hE hx, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_inter, Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2



/-! ## The suffix count through the vertex set -/

/-- Number of vertices of `V` in `[q, k - 1]` (interior vertices at or above `q`). -/
def suffixCount (k q : ℕ) (V : Finset (Vertex k)) : ℕ :=
  (V.filter (fun v => 0 < v.val ∧ v.val < k ∧ q ≤ v.val)).card

theorem suffixVisits_eq_suffixCount {m : ℕ} {p : Path k m} (hp : admissible k m p)
    (q : ℕ) : suffixVisits k m q p = suffixCount k q (vertexSet p) := by
  have hmono := admissible_strictMono hp
  have hzero : p (0 : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ k⟩ := hp.1
  have hlast : p (Fin.last m) = ⟨k, Nat.lt_succ_self k⟩ := hp.2.1
  unfold suffixVisits suffixCount
  apply Finset.card_bij (fun i _ => p i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hi0, him, hiq⟩ := hi
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, ?_, hiq⟩
    · unfold vertexSet
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · have h1 : p 0 < p i := hmono (Fin.lt_def.mpr hi0)
      rw [hzero] at h1
      exact h1
    · have h1 : p i < p (Fin.last m) := hmono (Fin.lt_def.mpr (by simpa using him))
      rw [hlast] at h1
      exact h1
  · intro i _ j _ h
    exact hmono.injective h
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hv, hv0, hvk, hvq⟩ := hv
    unfold vertexSet at hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, -, rfl⟩ := hv
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, hvq⟩
    · rcases Nat.eq_zero_or_pos i.val with h | h
      · exfalso
        have e : i = 0 := Fin.ext h
        rw [e, hzero] at hv0
        exact lt_irrefl _ hv0
      · exact h
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with h | h
      · exact h
      · exfalso
        have e : i = Fin.last m := Fin.ext h
        rw [e, hlast] at hvk
        exact lt_irrefl _ hvk

theorem suffixArray_stepKernel (θ : ℝ) (q : ℕ) (r s : ℕ) :
    suffixArray k q r s (stepKernel k θ)
      = ∑ V ∈ vertexSets k (r + 1),
          if suffixCount k q V = s then subWeight k θ V else 0 := by
  unfold suffixArray
  apply sum_paths_eq_sum_vertexSets
  intro p hp
  rw [suffixVisits_eq_suffixCount hp q, pathWeight_eq_subWeight hp θ]

theorem suffixCount_eq_sufN (q : ℕ) (V : Finset (Vertex k)) :
    suffixCount k q V = sufN q k (vertexNat V) := by
  unfold suffixCount sufN vertexNat
  rw [Finset.filter_image, Finset.card_image_of_injective _ Fin.val_injective]

theorem arith_evalS {t N p Np i j r r' s s' : ℕ} (hij : i + j ≤ N) (hj : j ≤ Np) (w : ℝ) :
    (if (t + (i + j) = r' + 2 ∧ t + (N - (i + j)) = r + 2) then
        ((if (p + j = s' ∧ p + (Np - j) = s) then (1 : ℝ) else 0)
          - (if (p + j = s ∧ p + (Np - j) = s') then 1 else 0)) * w
      else 0)
    = if (2 * t + N = r + r' + 4 ∧ 2 * p + Np = s + s') then
        ((if ((i : ℤ) = (r' : ℤ) + 2 - t - ((s' : ℤ) - p) ∧ (j : ℤ) = (s' : ℤ) - p) then w else 0)
          - (if ((i : ℤ) = (r' : ℤ) + 2 - t - ((s : ℤ) - p) ∧ (j : ℤ) = (s : ℤ) - p)
              then w else 0))
      else 0 := by
  split_ifs <;> first | (exfalso; omega) | ring

theorem Omega_evalS (ψ : ℝ) (k q r r' s s' : ℕ) (P₁ P₂ : Finset ℕ)
    (h0 : 0 ∈ P₁ ∩ P₂) (hk : k ∈ P₁ ∩ P₂)
    (hP₁ : P₁ ⊆ Finset.range (k + 1)) (hP₂ : P₂ ⊆ Finset.range (k + 1))
    {E : Finset ℕ} (hE : E ⊆ P₁ ∆ P₂) :
    Omega ψ k (sufN q k) r r' s s' ((P₁ ∩ P₂) ∪ E) ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))
      = if (2 * (P₁ ∩ P₂).card + (P₁ ∆ P₂).card = r + r' + 4
            ∧ 2 * sufN q k (P₁ ∩ P₂) + ((P₁ ∆ P₂).filter (fun v => ¬ v < q)).card = s + s') then
          ((if ((E ∩ (P₁ ∆ P₂).filter (fun v => v < q)).card : ℤ)
                  = (r' : ℤ) + 2 - (P₁ ∩ P₂).card - ((s' : ℤ) - sufN q k (P₁ ∩ P₂))
              ∧ ((E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card : ℤ)
                  = (s' : ℤ) - sufN q k (P₁ ∩ P₂)
            then bondWeight ψ (P₁ ∆ P₂) E else 0)
          - (if ((E ∩ (P₁ ∆ P₂).filter (fun v => v < q)).card : ℤ)
                  = (r' : ℤ) + 2 - (P₁ ∩ P₂).card - ((s : ℤ) - sufN q k (P₁ ∩ P₂))
              ∧ ((E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card : ℤ)
                  = (s : ℤ) - sufN q k (P₁ ∩ P₂)
            then bondWeight ψ (P₁ ∆ P₂) E else 0))
        else 0 := by
  obtain ⟨hcnt, hdiff⟩ := fibre_inv P₁ P₂ hE
  have hsym := ((cnt_eq_iff _ _ P₁ P₂).mp hcnt).2
  have hd := T_disj_D P₁ P₂
  have hTE : Disjoint (P₁ ∩ P₂) E := Finset.disjoint_of_subset_right hE hd
  have hTDE : Disjoint (P₁ ∩ P₂) ((P₁ ∆ P₂) \ E) :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset hd
  have h0D : 0 ∉ P₁ ∆ P₂ := fun h => Finset.disjoint_left.mp hd h0 h
  have hkD : k ∉ P₁ ∆ P₂ := fun h => Finset.disjoint_left.mp hd hk h
  have hDr : P₁ ∆ P₂ ⊆ Finset.range (k + 1) := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    rcases hx with h | h
    · exact hP₁ h.1
    · exact hP₂ h.1
  have hc1 : ((P₁ ∩ P₂) ∪ E).card = (P₁ ∩ P₂).card + E.card :=
    Finset.card_union_of_disjoint hTE
  have hc2 : ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)).card
      = (P₁ ∩ P₂).card + ((P₁ ∆ P₂) \ E).card := Finset.card_union_of_disjoint hTDE
  have hsd := Finset.card_sdiff_add_card_eq_card hE
  have hp1 : sufN q k ((P₁ ∩ P₂) ∪ E) = sufN q k (P₁ ∩ P₂) + sufN q k E := sufN_union hTE
  have hp2 : sufN q k ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))
      = sufN q k (P₁ ∩ P₂) + sufN q k ((P₁ ∆ P₂) \ E) := sufN_union hTDE
  have hpD : sufN q k (P₁ ∆ P₂) = sufN q k ((P₁ ∆ P₂) \ E) + sufN q k E := by
    rw [← sufN_union (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset hE]
  have hpE := sufN_eq_card_inter (q := q) hE hDr h0D hkD
  have hpDD := sufN_eq_card_inter (q := q) (Finset.Subset.refl (P₁ ∆ P₂)) hDr h0D hkD
  have hEc := card_split2 (fun v => v < q) hE
  have hDm : ((P₁ ∆ P₂) ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q))
      = (P₁ ∆ P₂).filter (fun v => ¬ v < q) :=
    Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  rw [hDm] at hpDD
  have hDc := card_split2 (fun v => v < q) (Finset.Subset.refl (P₁ ∆ P₂))
  rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
    Finset.inter_eq_right.mpr (Finset.filter_subset _ _)] at hDc
  have hij : (E ∩ (P₁ ∆ P₂).filter (fun v => v < q)).card
      + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card ≤ (P₁ ∆ P₂).card := by
    rw [← hEc]
    exact Finset.card_le_card hE
  have hj : (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card
      ≤ ((P₁ ∆ P₂).filter (fun v => ¬ v < q)).card :=
    Finset.card_le_card Finset.inter_subset_right
  have m1 : (0 ∈ (P₁ ∩ P₂) ∪ E) := Finset.mem_union_left _ h0
  have m2 : (k ∈ (P₁ ∩ P₂) ∪ E) := Finset.mem_union_left _ hk
  have m3 : (0 ∈ (P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) := Finset.mem_union_left _ h0
  have m4 : (k ∈ (P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) := Finset.mem_union_left _ hk
  unfold Omega
  rw [hsym, hdiff]
  simp only [m1, m2, m3, m4, and_self, true_and]
  have e1 : ((P₁ ∩ P₂) ∪ E).card
      = (P₁ ∩ P₂).card + ((E ∩ (P₁ ∆ P₂).filter (fun v => v < q)).card
          + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card) := by
    rw [hc1, ← hEc]
  have e2 : ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)).card
      = (P₁ ∩ P₂).card + ((P₁ ∆ P₂).card - ((E ∩ (P₁ ∆ P₂).filter (fun v => v < q)).card
          + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card)) := by
    rw [hc2, ← hEc]
    omega
  have e3 : sufN q k ((P₁ ∩ P₂) ∪ E)
      = sufN q k (P₁ ∩ P₂) + (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card := by
    rw [hp1, hpE]
  have e4 : sufN q k ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E))
      = sufN q k (P₁ ∩ P₂) + (((P₁ ∆ P₂).filter (fun v => ¬ v < q)).card
          - (E ∩ (P₁ ∆ P₂).filter (fun v => ¬ v < q)).card) := by
    rw [hp2]
    omega
  rw [e1, e2, e3, e4]
  exact arith_evalS hij hj _

open Classical in
theorem core_nonnegS {ψ : ℝ} (hψ1 : 1 ≤ ψ) (hψ2 : ψ ≤ 2) (k q r r' s s' : ℕ)
    (hr : r < r') (hs : s < s') (c : ℕ → ℕ) :
    0 ≤ ∑ U₁ ∈ (Finset.range (k + 1)).powerset, ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
      if cnt U₁ U₂ = c then Omega ψ k (sufN q k) r r' s s' U₁ U₂ else 0 := by
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
      (if cnt U₁ U₂ = cnt P₁ P₂ then Omega ψ k (sufN q k) r r' s s' U₁ U₂ else 0)
      = ∑ E ∈ (P₁ ∆ P₂).powerset,
          Omega ψ k (sufN q k) r r' s s' ((P₁ ∩ P₂) ∪ E) ((P₁ ∩ P₂) ∪ ((P₁ ∆ P₂) \ E)) := by
    rw [← Finset.sum_product' (Finset.range (k + 1)).powerset (Finset.range (k + 1)).powerset
      (fun U₁ U₂ => if cnt U₁ U₂ = cnt P₁ P₂ then Omega ψ k (sufN q k) r r' s s' U₁ U₂ else 0),
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
      show Omega ψ k (sufN q k) r r' s s' p.1 p.2 = Omega ψ k (sufN q k) r r' s s' _ _
      rw [← d1, ← d2]
  rw [hbij]
  -- evaluate every term
  rw [Finset.sum_congr rfl (fun E hE => Omega_evalS ψ k q r r' s s' P₁ P₂ h0 hk hP₁ hP₂
    (Finset.mem_powerset.mp hE))]
  set T := P₁ ∩ P₂ with hT
  set D := P₁ ∆ P₂ with hD
  set Dm := D.filter (fun v => v < q) with hDm
  set Dp := D.filter (fun v => ¬ v < q) with hDp
  have hU : Dm ∪ Dp = D := by
    ext x
    simp only [hDm, hDp, Finset.mem_union, Finset.mem_filter]
    tauto
  have hND : D.card = Dm.card + Dp.card := by
    have := card_split2 (fun v => v < q) (Finset.Subset.refl D)
    rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)] at this
    exact this
  have hDD : ∀ x ∈ Dm, ∀ y ∈ Dp, x < y := by
    intro x hx y hy
    rw [hDm, Finset.mem_filter] at hx
    rw [hDp, Finset.mem_filter] at hy
    omega
  by_cases hQ : (2 * T.card + D.card = r + r' + 4 ∧ 2 * sufN q k T + Dp.card = s + s')
  · simp only [hQ, and_self, ↓reduceIte]
    rw [Finset.sum_sub_distrib]
    have z1 := Zsum_eq_sum_D ψ hU ((r' : ℤ) + 2 - T.card - ((s' : ℤ) - sufN q k T))
      ((s' : ℤ) - sufN q k T)
    have z2 := Zsum_eq_sum_D ψ hU ((r' : ℤ) + 2 - T.card - ((s : ℤ) - sufN q k T))
      ((s : ℤ) - sufN q k T)
    rw [← z1, ← z2, sub_nonneg]
    obtain ⟨hQ1, hQ2⟩ := hQ
    exact Zsum_diff_nonneg_swap hψ1 hψ2 hDD (by omega) (by omega) (by omega) (by omega)
  · simp only [hQ, ↓reduceIte]
    simp

end CommonTime