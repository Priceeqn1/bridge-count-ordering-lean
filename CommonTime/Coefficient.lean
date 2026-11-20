import CommonTime.Grouping

/-!
# The polynomial bridge for Theorem 4.7(b), prefix clause
-/

open scoped symmDiff

namespace CommonTime

variable {k : ℕ}

/-! ## Transfer from `Finset (Vertex k)` to `Finset ℕ` -/

theorem card_vertexNat (V : Finset (Vertex k)) : (vertexNat V).card = V.card :=
  Finset.card_image_of_injective _ Fin.val_injective

theorem prefixCount_eq_pcN (q : ℕ) (V : Finset (Vertex k)) :
    prefixCount q V = pcN q (vertexNat V) := by
  unfold prefixCount pcN vertexNat
  rw [Finset.filter_image, Finset.card_image_of_injective _ Fin.val_injective]

theorem vertexNat_subset (V : Finset (Vertex k)) : vertexNat V ⊆ Finset.range (k + 1) := by
  intro n hn
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hn
  exact Finset.mem_range.mpr v.isLt

theorem mem_vertexNat {V : Finset (Vertex k)} {v : Vertex k} : v.val ∈ vertexNat V ↔ v ∈ V := by
  unfold vertexNat
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    rwa [Fin.ext hwv] at hw
  · intro h
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

/-- Sums over vertex sets are sums over subsets of `{0, …, k}`. -/
theorem sum_vertexSets (m : ℕ) (F : Finset ℕ → ℝ) :
    ∑ V ∈ vertexSets k m, F (vertexNat V)
      = ∑ U ∈ (Finset.range (k + 1)).powerset,
          if (0 ∈ U ∧ k ∈ U ∧ U.card = m + 1) then F U else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij (fun V => vertexNat V)
  · intro V hV
    rw [mem_vertexSets] at hV
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨vertexNat_subset V, ?_, ?_, ?_⟩
    · exact mem_vertexNat.mpr hV.1
    · exact mem_vertexNat.mpr hV.2.1
    · rw [card_vertexNat]
      exact hV.2.2
  · intro V₁ _ V₂ _ h
    exact Finset.image_injective Fin.val_injective h
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hU
    obtain ⟨hsub, h0, hk, hcard⟩ := hU
    refine ⟨Finset.univ.filter (fun v : Vertex k => v.val ∈ U), ?_, ?_⟩
    · have hv : vertexNat (Finset.univ.filter (fun v : Vertex k => v.val ∈ U)) = U := by
        ext n
        unfold vertexNat
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact hv
        · intro hn
          exact ⟨⟨n, Finset.mem_range.mp (hsub hn)⟩, hn, rfl⟩
      rw [Finset.mem_coe, mem_vertexSets]
      refine ⟨?_, ?_, ?_⟩
      · simpa using h0
      · simpa using hk
      · rw [← card_vertexNat, hv]
        exact hcard
    · ext n
      unfold vertexNat
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hv
      · intro hn
        exact ⟨⟨n, Finset.mem_range.mp (hsub hn)⟩, hn, rfl⟩
  · intro V _
    rfl

/-! ## Activity monomials -/

/-- Exponent vector of `∏_{v ∈ V ∖ {k}} activity v`. -/
noncomputable def expo (V : Finset (Vertex k)) : Fin (k + 1) →₀ ℕ :=
  ∑ v ∈ (V.erase ⟨k, Nat.lt_succ_self k⟩).filter (fun v => v.val ≠ 0), Finsupp.single v 1

theorem actProd_eq (V : Finset (Vertex k)) :
    ∏ v ∈ V.erase ⟨k, Nat.lt_succ_self k⟩, activity v
      = MvPolynomial.monomial (expo V) (1 : ℝ) := by
  unfold expo
  rw [MvPolynomial.monomial_sum_one, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  unfold activity
  by_cases h : v.val = 0
  · simp [h]
  · simp [h, MvPolynomial.X]

theorem expo_apply (V : Finset (Vertex k)) (j : Vertex k) :
    expo V j = if (j ∈ V ∧ j ≠ ⟨k, Nat.lt_succ_self k⟩ ∧ j.val ≠ 0) then 1 else 0 := by
  unfold expo
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_erase]
  by_cases h1 : j ∈ V <;> by_cases h2 : j = ⟨k, Nat.lt_succ_self k⟩ <;>
    by_cases h3 : j.val = 0 <;> simp [h1, h2, h3]

theorem expo_add_apply (A B : Finset (Vertex k)) (j : Vertex k) :
    (expo A + expo B) j
      = if (j ≠ ⟨k, Nat.lt_succ_self k⟩ ∧ j.val ≠ 0)
          then cnt (vertexNat A) (vertexNat B) j.val else 0 := by
  rw [Finsupp.add_apply, expo_apply, expo_apply]
  unfold cnt
  simp only [mem_vertexNat]
  by_cases h1 : j ∈ A <;> by_cases h2 : j ∈ B <;>
    by_cases h3 : j = ⟨k, Nat.lt_succ_self k⟩ <;> by_cases h4 : j.val = 0 <;>
    simp [h1, h2, h3, h4]

theorem cnt_at_endpoints {A B : Finset (Vertex k)}
    (hA0 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ A) (hAk : (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ A)
    (hB0 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ B) (hBk : (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ B) :
    cnt (vertexNat A) (vertexNat B) 0 = 2 ∧ cnt (vertexNat A) (vertexNat B) k = 2 := by
  unfold cnt
  have a0 : 0 ∈ vertexNat A := mem_vertexNat.mpr hA0
  have ak : k ∈ vertexNat A := mem_vertexNat.mpr hAk
  have b0 : 0 ∈ vertexNat B := mem_vertexNat.mpr hB0
  have bk : k ∈ vertexNat B := mem_vertexNat.mpr hBk
  simp [a0, ak, b0, bk]

theorem cnt_out {A B : Finset (Vertex k)} {n : ℕ} (hn : ¬ n < k + 1) :
    cnt (vertexNat A) (vertexNat B) n = 0 := by
  unfold cnt
  have h1 : n ∉ vertexNat A := fun h => hn (Finset.mem_range.mp (vertexNat_subset A h))
  have h2 : n ∉ vertexNat B := fun h => hn (Finset.mem_range.mp (vertexNat_subset B h))
  simp [h1, h2]

/-- Equal exponent vectors are equal multiplicity patterns (for sets containing both
    endpoints). -/
theorem expo_eq_iff_cnt_eq {A B A₀ B₀ : Finset (Vertex k)} (hk : 1 ≤ k)
    (hA0 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ A) (hAk : (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ A)
    (hB0 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ B) (hBk : (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ B)
    (hA0' : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ A₀) (hAk' : (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ A₀)
    (hB0' : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ B₀) (hBk' : (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ B₀) :
    expo A + expo B = expo A₀ + expo B₀
      ↔ cnt (vertexNat A) (vertexNat B) = cnt (vertexNat A₀) (vertexNat B₀) := by
  obtain ⟨e0, ek⟩ := cnt_at_endpoints hA0 hAk hB0 hBk
  obtain ⟨e0', ek'⟩ := cnt_at_endpoints hA0' hAk' hB0' hBk'
  constructor
  · intro h
    funext n
    by_cases hn : n < k + 1
    · by_cases hn0 : n = 0
      · subst hn0
        rw [e0, e0']
      · by_cases hnk : n = k
        · subst hnk
          rw [ek, ek']
        · have hj := congrArg (fun f => f ⟨n, hn⟩) h
          simp only [expo_add_apply] at hj
          have hc : (⟨n, hn⟩ : Vertex k) ≠ ⟨k, Nat.lt_succ_self k⟩ ∧ (⟨n, hn⟩ : Vertex k).val ≠ 0 := by
            refine ⟨?_, ?_⟩
            · intro hh
              exact hnk (Fin.mk.inj hh)
            · exact hn0
          rw [ite_eq_left hc, ite_eq_left hc] at hj
          exact hj
    · rw [cnt_out hn, cnt_out hn]
  · intro h
    ext j
    rw [Finsupp.add_apply, Finsupp.add_apply] at *
    have := expo_add_apply A B j
    have h2 := expo_add_apply A₀ B₀ j
    rw [Finsupp.add_apply] at this h2
    rw [this, h2, h]

open Classical in
theorem coeff_pair (θ : ℝ) (hθ : θ ≠ 0) (A B : Finset (Vertex k))
    (h1 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ A)
    (h2 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ B) (e : Fin (k + 1) →₀ ℕ) :
    (subWeight k θ A * subWeight k θ B).coeff e
      = (θ ^ (A.card - 1) * θ ^ (B.card - 1)
          * ((θ⁻¹) ^ baseCount (vertexNat A) (vertexNat B)
            * bondWeight θ⁻¹ (vertexNat A ∆ vertexNat B) (vertexNat A \ vertexNat B)))
        * (if expo A + expo B = e then 1 else 0) := by
  rw [subWeight_pair θ hθ A B h1 h2, actProd_eq A, actProd_eq B, MvPolynomial.monomial_mul,
    mul_one, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]

theorem baseCount_eq_range {U₁ U₂ : Finset ℕ} (h1 : U₁ ⊆ Finset.range (k + 1))
    (h2 : U₂ ⊆ Finset.range (k + 1)) :
    baseCount U₁ U₂
      = ∑ u ∈ Finset.range (k + 1), bondBase (cnt U₁ U₂ u) (cnt U₁ U₂ (u + 1)) := by
  unfold baseCount
  apply Finset.sum_subset (Finset.union_subset h1 h2)
  intro u _ hu
  have h1' : u ∉ U₁ := fun h => hu (Finset.mem_union_left _ h)
  have h2' : u ∉ U₂ := fun h => hu (Finset.mem_union_right _ h)
  unfold cnt bondBase
  simp [h1', h2']

/-! ## Expansion of the minor -/

theorem sum_mul_sum_swap {ι κ : Type*} (S : Finset ι) (T : Finset κ) (f : ι → Poly k)
    (g : κ → Poly k) :
    (∑ B ∈ S, f B) * (∑ A ∈ T, g A) = ∑ A ∈ T, ∑ B ∈ S, g A * f B := by
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  exact mul_comm _ _

theorem ite_mul_ite' {α : Type*} [MulZeroClass α] (a b : Prop) [Decidable a] [Decidable b]
    (x y : α) : (if a then x else 0) * (if b then y else 0) = if a ∧ b then x * y else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem minor_expand (θ : ℝ) (q : ℕ) (hqk : q < k) (r r' s s' : ℕ) :
    minor (prefixArray k q r s (stepKernel k θ)) (prefixArray k q r s' (stepKernel k θ))
      (prefixArray k q r' s (stepKernel k θ)) (prefixArray k q r' s' (stepKernel k θ))
      = ∑ A ∈ vertexSets k (r' + 1), ∑ B ∈ vertexSets k (r + 1),
          ((if prefixCount q A = s' ∧ prefixCount q B = s
              then subWeight k θ A * subWeight k θ B else 0)
            - (if prefixCount q A = s ∧ prefixCount q B = s'
              then subWeight k θ A * subWeight k θ B else 0)) := by
  unfold minor
  rw [prefixArray_stepKernel θ q hqk r s, prefixArray_stepKernel θ q hqk r s',
    prefixArray_stepKernel θ q hqk r' s, prefixArray_stepKernel θ q hqk r' s',
    sum_mul_sum_swap, sum_mul_sum_swap, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro B _
  rw [ite_mul_ite', ite_mul_ite']

/-! ## The coefficient is a nonnegative multiple of the core sum -/

open Classical in
/-- Grouped summand: the coefficient contribution of a pair `(U₁, U₂)` of vertex sets
    (as subsets of `ℕ`) to the monomial with multiplicity pattern `c`. -/
noncomputable def Psi (θ ψ : ℝ) (pc : Finset ℕ → ℕ) (r r' s s' : ℕ) (c : ℕ → ℕ)
    (U₁ U₂ : Finset ℕ) : ℝ :=
  ((if pc U₁ = s' ∧ pc U₂ = s then (1 : ℝ) else 0)
      - (if pc U₁ = s ∧ pc U₂ = s' then 1 else 0))
    * (θ ^ (U₁.card - 1) * θ ^ (U₂.card - 1)
        * (ψ ^ baseCount U₁ U₂ * bondWeight ψ (U₁ ∆ U₂) (U₁ \ U₂)))
    * (if cnt U₁ U₂ = c then 1 else 0)

theorem Omega_of_conds {ψ : ℝ} {k : ℕ} {pc : Finset ℕ → ℕ} {r r' s s' : ℕ} {U₁ U₂ : Finset ℕ}
    (c₁ : 0 ∈ U₁ ∧ k ∈ U₁ ∧ U₁.card = r' + 1 + 1)
    (c₂ : 0 ∈ U₂ ∧ k ∈ U₂ ∧ U₂.card = r + 1 + 1) :
    Omega ψ k pc r r' s s' U₁ U₂
      = ((if pc U₁ = s' ∧ pc U₂ = s then (1 : ℝ) else 0)
          - (if pc U₁ = s ∧ pc U₂ = s' then 1 else 0))
          * bondWeight ψ (U₁ ∆ U₂) (U₁ \ U₂) := by
  unfold Omega
  rw [ite_eq_left ⟨⟨c₁.1, c₁.2.1, c₂.1, c₂.2.1⟩, by omega, by omega⟩]

theorem Omega_of_not {ψ : ℝ} {k : ℕ} {pc : Finset ℕ → ℕ} {r r' s s' : ℕ} {U₁ U₂ : Finset ℕ}
    (h : ¬ ((0 ∈ U₁ ∧ k ∈ U₁ ∧ U₁.card = r' + 1 + 1) ∧ (0 ∈ U₂ ∧ k ∈ U₂ ∧ U₂.card = r + 1 + 1))) :
    Omega ψ k pc r r' s s' U₁ U₂ = 0 := by
  unfold Omega
  apply ite_eq_right
  rintro ⟨⟨a, b, c, d⟩, e, f⟩
  exact h ⟨⟨a, b, by omega⟩, ⟨c, d, by omega⟩⟩

theorem sum_pairs_transfer (m' m : ℕ) (Ψ : Finset ℕ → Finset ℕ → ℝ) :
    ∑ A ∈ vertexSets k m', ∑ B ∈ vertexSets k m, Ψ (vertexNat A) (vertexNat B)
      = ∑ U₁ ∈ (Finset.range (k + 1)).powerset,
          if (0 ∈ U₁ ∧ k ∈ U₁ ∧ U₁.card = m' + 1) then
            ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
              (if (0 ∈ U₂ ∧ k ∈ U₂ ∧ U₂.card = m + 1) then Ψ U₁ U₂ else 0)
          else 0 := by
  rw [Finset.sum_congr rfl (fun A _ => sum_vertexSets m (fun U₂ => Ψ (vertexNat A) U₂))]
  exact sum_vertexSets m' (fun U₁ => ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
    (if (0 ∈ U₂ ∧ k ∈ U₂ ∧ U₂.card = m + 1) then Ψ U₁ U₂ else 0))

open Classical in
/-- **Coefficientwise nonnegativity of the expanded minor**, for any count function
    `pc` on subsets of `ℕ` for which the combinatorial core inequality holds. -/
theorem coeff_expanded_nonneg {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 1)
    (hk : 1 ≤ k) (pcV : Finset (Vertex k) → ℕ) (pc : Finset ℕ → ℕ)
    (hpc : ∀ V, pcV V = pc (vertexNat V)) (r r' s s' : ℕ)
    (hcore : ∀ c : ℕ → ℕ, 0 ≤ ∑ U₁ ∈ (Finset.range (k + 1)).powerset,
      ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
        if cnt U₁ U₂ = c then Omega θ⁻¹ k pc r r' s s' U₁ U₂ else 0)
    (e : Fin (k + 1) →₀ ℕ) :
    0 ≤ (∑ A ∈ vertexSets k (r' + 1), ∑ B ∈ vertexSets k (r + 1),
          ((if pcV A = s' ∧ pcV B = s
              then subWeight k θ A * subWeight k θ B else 0)
            - (if pcV A = s ∧ pcV B = s'
              then subWeight k θ A * subWeight k θ B else 0))).coeff e := by
  have hψ1 : 1 ≤ θ⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hθ0]
    linarith
  have hψ2 : θ⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hθ0]
    linarith
  have hite : ∀ (P : Prop) [Decidable P] (x : Poly k),
      (if P then x else 0).coeff e = if P then x.coeff e else 0 := by
    intro P _ x
    by_cases h : P <;> simp [h]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_sub, hite]
  have step1 : ∀ A ∈ vertexSets k (r' + 1), ∀ B ∈ vertexSets k (r + 1),
      ((if pcV A = s' ∧ pcV B = s
          then (subWeight k θ A * subWeight k θ B).coeff e else 0)
        - (if pcV A = s ∧ pcV B = s'
          then (subWeight k θ A * subWeight k θ B).coeff e else 0))
      = ((if pcV A = s' ∧ pcV B = s then (1 : ℝ) else 0)
          - (if pcV A = s ∧ pcV B = s' then 1 else 0))
        * ((θ ^ (A.card - 1) * θ ^ (B.card - 1)
            * ((θ⁻¹) ^ baseCount (vertexNat A) (vertexNat B)
              * bondWeight θ⁻¹ (vertexNat A ∆ vertexNat B) (vertexNat A \ vertexNat B)))
          * (if expo A + expo B = e then 1 else 0)) := by
    intro A hA B hB
    rw [mem_vertexSets] at hA hB
    rw [coeff_pair θ hθ0.ne' A B hA.1 hB.1 e]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun A hA => Finset.sum_congr rfl (fun B hB => step1 A hA B hB))]
  by_cases hX : ∃ A ∈ vertexSets k (r' + 1), ∃ B ∈ vertexSets k (r + 1), expo A + expo B = e
  swap
  · apply le_of_eq
    symm
    apply Finset.sum_eq_zero
    intro A hA
    apply Finset.sum_eq_zero
    intro B hB
    have : ¬ (expo A + expo B = e) := fun h => hX ⟨A, hA, B, hB, h⟩
    rw [ite_eq_right this]
    ring
  obtain ⟨A₀, hA₀, B₀, hB₀, he⟩ := hX
  subst he
  rw [mem_vertexSets] at hA₀ hB₀
  set c : ℕ → ℕ := cnt (vertexNat A₀) (vertexNat B₀) with hc
  have step2 : ∀ A ∈ vertexSets k (r' + 1), ∀ B ∈ vertexSets k (r + 1),
      ((if pcV A = s' ∧ pcV B = s then (1 : ℝ) else 0)
          - (if pcV A = s ∧ pcV B = s' then 1 else 0))
        * ((θ ^ (A.card - 1) * θ ^ (B.card - 1)
            * ((θ⁻¹) ^ baseCount (vertexNat A) (vertexNat B)
              * bondWeight θ⁻¹ (vertexNat A ∆ vertexNat B) (vertexNat A \ vertexNat B)))
          * (if expo A + expo B = expo A₀ + expo B₀ then 1 else 0))
      = Psi θ θ⁻¹ pc r r' s s' c (vertexNat A) (vertexNat B) := by
    intro A hA B hB
    rw [mem_vertexSets] at hA hB
    have hiff := expo_eq_iff_cnt_eq hk hA.1 hA.2.1 hB.1 hB.2.1 hA₀.1 hA₀.2.1 hB₀.1 hB₀.2.1
    unfold Psi
    simp only [hiff, card_vertexNat, hpc]
    ring
  rw [Finset.sum_congr rfl (fun A hA => Finset.sum_congr rfl (fun B hB => step2 A hA B hB))]
  rw [sum_pairs_transfer (r' + 1) (r + 1)
    (fun U₁ U₂ => Psi θ θ⁻¹ pc r r' s s' c U₁ U₂)]
  -- compare with the core sum
  set Bc : ℕ := ∑ u ∈ Finset.range (k + 1), bondBase (c u) (c (u + 1)) with hBc
  have hκ : 0 ≤ θ ^ (r' + 1) * θ ^ (r + 1) * (θ⁻¹) ^ Bc := by positivity
  have key : ∀ U₁ ∈ (Finset.range (k + 1)).powerset,
      (if (0 ∈ U₁ ∧ k ∈ U₁ ∧ U₁.card = r' + 1 + 1) then
        ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
          (if (0 ∈ U₂ ∧ k ∈ U₂ ∧ U₂.card = r + 1 + 1)
            then Psi θ θ⁻¹ pc r r' s s' c U₁ U₂ else 0)
        else 0)
      = ∑ U₂ ∈ (Finset.range (k + 1)).powerset,
          (θ ^ (r' + 1) * θ ^ (r + 1) * (θ⁻¹) ^ Bc)
            * (if cnt U₁ U₂ = c then Omega θ⁻¹ k pc r r' s s' U₁ U₂ else 0) := by
    intro U₁ hU₁
    rw [Finset.mem_powerset] at hU₁
    by_cases c₁ : (0 ∈ U₁ ∧ k ∈ U₁ ∧ U₁.card = r' + 1 + 1)
    · rw [ite_eq_left c₁]
      apply Finset.sum_congr rfl
      intro U₂ hU₂
      rw [Finset.mem_powerset] at hU₂
      by_cases c₂ : (0 ∈ U₂ ∧ k ∈ U₂ ∧ U₂.card = r + 1 + 1)
      · rw [ite_eq_left c₂]
        by_cases hcc : cnt U₁ U₂ = c
        · rw [ite_eq_left hcc, Omega_of_conds c₁ c₂]
          unfold Psi
          rw [ite_eq_left hcc, baseCount_eq_range hU₁ hU₂, hcc]
          have e1 : U₁.card - 1 = r' + 1 := by omega
          have e2 : U₂.card - 1 = r + 1 := by omega
          rw [e1, e2]
          ring
        · rw [ite_eq_right hcc]
          unfold Psi
          rw [ite_eq_right hcc]
          ring
      · rw [ite_eq_right c₂]
        by_cases hcc : cnt U₁ U₂ = c
        · rw [ite_eq_left hcc, Omega_of_not (fun h => c₂ h.2)]
          ring
        · rw [ite_eq_right hcc]
          ring
    · rw [ite_eq_right c₁]
      symm
      apply Finset.sum_eq_zero
      intro U₂ _
      by_cases hcc : cnt U₁ U₂ = c
      · rw [ite_eq_left hcc, Omega_of_not (fun h => c₁ h.1)]
        ring
      · rw [ite_eq_right hcc]
        ring
  rw [Finset.sum_congr rfl key]
  simp only [← Finset.mul_sum]
  exact mul_nonneg hκ (hcore c)

/-- **Prefix clause of Theorem 4.7(b), coefficientwise.** -/
theorem coeff_minor_nonneg {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 1)
    {q : ℕ} (hqk : q < k) (hk : 1 ≤ k) (r r' s s' : ℕ) (hr : r < r') (hs : s < s')
    (e : Fin (k + 1) →₀ ℕ) :
    0 ≤ (minor (prefixArray k q r s (stepKernel k θ)) (prefixArray k q r s' (stepKernel k θ))
      (prefixArray k q r' s (stepKernel k θ)) (prefixArray k q r' s' (stepKernel k θ))).coeff e := by
  have hψ1 : 1 ≤ θ⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hθ0]
    linarith
  have hψ2 : θ⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hθ0]
    linarith
  rw [minor_expand θ q hqk r r' s s']
  exact coeff_expanded_nonneg hθ0 hθ1 hθ2 hk (prefixCount q) (pcN q)
    (prefixCount_eq_pcN q) r r' s s'
    (fun c => core_nonneg hψ1 hψ2 k q r r' s s' hr hs c) e

/-- **Theorem 4.7(b), prefix clause, `1/2 ≤ θ ≤ 1`.** For the Toeplitz kernel of
    display (28) and every prefix interval `[1, q]`, the count-array minor is
    coefficientwise nonnegative. -/
theorem toeplitz_prefix_count_array_TP2 {θ : ℝ} (hθ1 : 1 / 2 ≤ θ) (hθ2 : θ ≤ 1)
    {k q : ℕ} (hq0 : 1 ≤ q) (hqk : q < k) (r r' s s' : ℕ) (hr : r < r') (hs : s < s') :
    CoeffNonneg (minor (prefixArray k q r s (stepKernel k θ))
      (prefixArray k q r s' (stepKernel k θ))
      (prefixArray k q r' s (stepKernel k θ)) (prefixArray k q r' s' (stepKernel k θ))) :=
  fun e => coeff_minor_nonneg (by linarith) hθ1 hθ2 hqk (by omega) r r' s s' hr hs e

end CommonTime