import CommonTime.ChainEnum

/-!
# Bond factorization (Theorem 4.7, step 5b)

Two vertex sets `V₁, V₂ ⊆ ℕ` (subsets of `{0, …, k}`) are covered by the
multiplicity `c(x) = 1{x ∈ V₁} + 1{x ∈ V₂} ∈ {0, 1, 2}`. Let
`D = V₁ ∆ V₂ = {c = 1}` and `E = V₁ \ V₂ ⊆ D` (the sites of `D` carried by
`V₁`, i.e. the `η = 1` sites).

* `pair_bond_factor` : `ψ^(adj V₁ + adj V₂) = ψ^(C₀) * bondWeight ψ D E`,
  where `adj V = #{u ∈ V : u + 1 ∈ V}` and
  `C₀ = Σ_u f(c(u), c(u+1))` with `f(2,2) = 2`, `f(2,1) = f(1,2) = 1`, else `0`.
  Only bonds between two singly covered sites depend on `η`.
* `bondWeight_split` : for `D₋ < D₊` the bond weight of `D₋ ∪ D₊` is the
  product of the two bond weights and the cut factor.
* `Zsum_eq_Zpair` : the weight sum over `E ⊆ D₋ ∪ D₊` with
  `|E ∩ D₋| = i`, `|E ∩ D₊| = j` is `Zpair κ (enumState D₋ max) (enumState D₊ min)`
  with `κ = ψ` if the two cut sites are adjacent integers and `1` otherwise.
-/

open scoped symmDiff

namespace CommonTime

/-! ## Pair identity -/

/-- `adj V = #{u ∈ V : u + 1 ∈ V}`. -/
def adjCount (V : Finset ℕ) : ℕ := (V.filter (fun u => u + 1 ∈ V)).card

/-- The multiplicity `c(x) = 1{x ∈ V₁} + 1{x ∈ V₂}`. -/
def cnt (V₁ V₂ : Finset ℕ) (x : ℕ) : ℕ :=
  (if x ∈ V₁ then 1 else 0) + (if x ∈ V₂ then 1 else 0)

/-- Bond contribution `f(a, b)` of two neighbouring multiplicities that does not
    depend on the bits: `f(2,2) = 2`, `f(2,1) = f(1,2) = 1`, otherwise `0`. -/
def bondBase (a b : ℕ) : ℕ :=
  if a = 2 ∧ b = 2 then 2 else if (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) then 1 else 0

/-- `C₀(c) = Σ_u f(c(u), c(u+1))`. -/
def baseCount (V₁ V₂ : Finset ℕ) : ℕ :=
  ∑ u ∈ V₁ ∪ V₂, bondBase (cnt V₁ V₂ u) (cnt V₁ V₂ (u + 1))

/-- The bond weight is a power of `ψ`. -/
theorem bondWeight_eq_pow (ψ : ℝ) (D E : Finset ℕ) :
    bondWeight ψ D E
      = ψ ^ (D.filter (fun u => u + 1 ∈ D ∧ (u ∈ E ↔ u + 1 ∈ E))).card := by
  unfold bondWeight
  have h : ∀ u ∈ D, ∏ j ∈ D, bondFactor ψ E u j
      = if (u + 1 ∈ D ∧ (u ∈ E ↔ u + 1 ∈ E)) then ψ else 1 := by
    intro u _
    by_cases hu : u + 1 ∈ D
    · rw [Finset.prod_eq_single_of_mem (u + 1) hu]
      · unfold bondFactor
        simp [hu]
      · intro j _ hne
        unfold bondFactor
        exact ite_eq_right (fun h => hne h.1.symm)
    · rw [Finset.prod_eq_one]
      · simp [hu]
      · intro j hj
        unfold bondFactor
        apply ite_eq_right
        intro h
        exact hu (h.1 ▸ hj)
  rw [Finset.prod_congr rfl h, Finset.prod_ite]
  simp

/-- Bond-by-bond identity. -/
theorem bond_pointwise (V₁ V₂ : Finset ℕ) (u : ℕ) :
    (if u ∈ V₁ ∧ u + 1 ∈ V₁ then 1 else 0) + (if u ∈ V₂ ∧ u + 1 ∈ V₂ then 1 else 0)
      = bondBase (cnt V₁ V₂ u) (cnt V₁ V₂ (u + 1))
        + (if (u ∈ V₁ ∆ V₂ ∧ u + 1 ∈ V₁ ∆ V₂ ∧ (u ∈ V₁ \ V₂ ↔ u + 1 ∈ V₁ \ V₂))
            then 1 else 0) := by
  by_cases a : u ∈ V₁ <;> by_cases b : u ∈ V₂ <;> by_cases c : u + 1 ∈ V₁ <;>
    by_cases d : u + 1 ∈ V₂ <;>
    simp [cnt, bondBase, Finset.mem_symmDiff, Finset.mem_sdiff, a, b, c, d]

/-- `adj V` as a sum over any finite superset. -/
theorem adjCount_eq_sum {V S : Finset ℕ} (h : V ⊆ S) :
    adjCount V = ∑ u ∈ S, if u ∈ V ∧ u + 1 ∈ V then 1 else 0 := by
  unfold adjCount
  rw [Finset.card_filter]
  symm
  rw [← Finset.sum_subset h]
  · apply Finset.sum_congr rfl
    intro u hu
    simp [hu]
  · intro u _ hu
    simp [hu]

theorem pair_exponent (V₁ V₂ : Finset ℕ) :
    adjCount V₁ + adjCount V₂
      = baseCount V₁ V₂
        + ((V₁ ∆ V₂).filter
            (fun u => u + 1 ∈ V₁ ∆ V₂ ∧ (u ∈ V₁ \ V₂ ↔ u + 1 ∈ V₁ \ V₂))).card := by
  have hD : V₁ ∆ V₂ ⊆ V₁ ∪ V₂ := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    rw [Finset.mem_union]
    tauto
  rw [adjCount_eq_sum (Finset.subset_union_left (s₂ := V₂)),
    adjCount_eq_sum (Finset.subset_union_right (s₁ := V₁)), ← Finset.sum_add_distrib]
  unfold baseCount
  rw [Finset.card_filter]
  have e : ∀ u ∈ V₁ ∪ V₂,
      ((if u ∈ V₁ ∧ u + 1 ∈ V₁ then 1 else 0) + (if u ∈ V₂ ∧ u + 1 ∈ V₂ then 1 else 0))
        = bondBase (cnt V₁ V₂ u) (cnt V₁ V₂ (u + 1))
          + (if (u ∈ V₁ ∆ V₂ ∧ u + 1 ∈ V₁ ∆ V₂ ∧ (u ∈ V₁ \ V₂ ↔ u + 1 ∈ V₁ \ V₂))
              then 1 else 0) := fun u _ => bond_pointwise V₁ V₂ u
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_subset hD]
  · apply Finset.sum_congr rfl
    intro u hu
    simp [hu]
  · intro u _ hu
    simp [hu]

/-- **Pair identity.** The `ψ`-weight of a pair of paths is `ψ^{C₀}` times the
    bond weight of the singly covered sites. -/
theorem pair_bond_factor (ψ : ℝ) (V₁ V₂ : Finset ℕ) :
    ψ ^ adjCount V₁ * ψ ^ adjCount V₂
      = ψ ^ baseCount V₁ V₂ * bondWeight ψ (V₁ ∆ V₂) (V₁ \ V₂) := by
  rw [← pow_add, pair_exponent, pow_add, bondWeight_eq_pow]

/-! ## Splitting at the cut -/

/-- If every site of `A` lies below every site of `B`, the bond weight of
    `A ∪ B` is the product of the two bond weights and the single cut bond
    between `max A` and `min B`. -/
theorem bondWeight_split (ψ : ℝ) {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x < y) (E : Finset ℕ) :
    bondWeight ψ (A ∪ B) E
      = bondWeight ψ A E * bondWeight ψ B E
        * (if A.max' hA + 1 = B.min' hB ∧ (A.max' hA ∈ E ↔ B.min' hB ∈ E) then ψ else 1) := by
  have hdisj : Disjoint A B :=
    Finset.disjoint_left.mpr (fun x hx hxB => lt_irrefl x (hAB x hx x hxB))
  have hmm : A.max' hA < B.min' hB :=
    hAB _ (Finset.max'_mem A hA) _ (Finset.min'_mem B hB)
  have h1 : ∏ u ∈ B, ∏ j ∈ A, bondFactor ψ E u j = 1 := by
    apply Finset.prod_eq_one
    intro u hu
    apply Finset.prod_eq_one
    intro j hj
    unfold bondFactor
    apply ite_eq_right
    intro h
    have := hAB j hj u hu
    omega
  have h2 : ∏ u ∈ A, ∏ j ∈ B, bondFactor ψ E u j
      = bondFactor ψ E (A.max' hA) (B.min' hB) := by
    rw [Finset.prod_eq_single_of_mem (A.max' hA) (Finset.max'_mem A hA)]
    · rw [Finset.prod_eq_single_of_mem (B.min' hB) (Finset.min'_mem B hB)]
      intro j hj hne
      unfold bondFactor
      apply ite_eq_right
      intro h
      have := Finset.min'_le B j hj
      omega
    · intro u hu hne
      apply Finset.prod_eq_one
      intro j hj
      unfold bondFactor
      apply ite_eq_right
      intro h
      have h3 := Finset.le_max' A u hu
      have h4 := Finset.min'_le B j hj
      omega
  have h3 : bondFactor ψ E (A.max' hA) (B.min' hB)
      = if A.max' hA + 1 = B.min' hB ∧ (A.max' hA ∈ E ↔ B.min' hB ∈ E) then ψ else 1 := rfl
  have hu : ∀ u, ∏ j ∈ A ∪ B, bondFactor ψ E u j
      = (∏ j ∈ A, bondFactor ψ E u j) * ∏ j ∈ B, bondFactor ψ E u j :=
    fun u => Finset.prod_union hdisj
  unfold bondWeight
  rw [Finset.prod_union hdisj]
  simp only [hu, Finset.prod_mul_distrib, h1, h2, h3]
  ring

/-! ## The weight sum over a split site set -/

/-- `Z(i, j)`: total bond weight of `E ⊆ D₋ ∪ D₊` with `|E ∩ D₋| = i`,
    `|E ∩ D₊| = j`. -/
def Zsum (ψ : ℝ) (Dm Dp : Finset ℕ) (i j : ℤ) : ℝ :=
  ∑ E ∈ (Dm ∪ Dp).powerset,
    if ((E ∩ Dm).card : ℤ) = i ∧ ((E ∩ Dp).card : ℤ) = j
      then bondWeight ψ (Dm ∪ Dp) E else 0

/-- Reindex subsets of a disjoint union as pairs of subsets. -/
theorem sum_powerset_union {Dm Dp : Finset ℕ} (hdisj : Disjoint Dm Dp)
    (F : Finset ℕ → ℝ) :
    ∑ E ∈ (Dm ∪ Dp).powerset, F E
      = ∑ p ∈ Dm.powerset ×ˢ Dp.powerset, F (p.1 ∪ p.2) := by
  symm
  refine Finset.sum_bij' (fun p _ => p.1 ∪ p.2) (fun E _ => (E ∩ Dm, E ∩ Dp))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    rw [Finset.mem_powerset]
    exact Finset.union_subset_union hp.1 hp.2
  · intro E hE
    rw [Finset.mem_powerset] at hE
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    obtain ⟨h1, h2⟩ := hp
    ext x
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (Finset.disjoint_right.mp hdisj (h2 h))
      · intro h
        exact ⟨Or.inl h, h1 h⟩
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd hx (Finset.disjoint_left.mp hdisj (h1 h))
        · exact h
      · intro h
        exact ⟨Or.inr h, h2 h⟩
  · intro E hE
    rw [Finset.mem_powerset] at hE
    show (E ∩ Dm) ∪ (E ∩ Dp) = E
    rw [← Finset.inter_union_distrib_left]
    exact Finset.inter_eq_left.mpr hE
  · intro p _
    rfl

/-- **Bridge to the chain lemma.** The weight sum `Z(i, j)` is the coupled-chain
    quantity `Zpair κ A B i j`, where `A` is the enumeration state of `D₋` with
    its top site designated (the site next to the cut), `B` that of `D₊` with its
    bottom site designated, and `κ = ψ` if the two cut sites are adjacent
    integers, `1` otherwise. -/
theorem Zsum_eq_Zpair (ψ : ℝ) {Dm Dp : Finset ℕ} (hm : Dm.Nonempty) (hp : Dp.Nonempty)
    (hDD : ∀ x ∈ Dm, ∀ y ∈ Dp, x < y) (i j : ℤ) :
    Zsum ψ Dm Dp i j
      = Zpair (if Dm.max' hm + 1 = Dp.min' hp then ψ else 1)
          (enumState ψ Dm (Dm.max' hm)) (enumState ψ Dp (Dp.min' hp)) i j := by
  have hdisj : Disjoint Dm Dp :=
    Finset.disjoint_left.mpr (fun x hx hxB => lt_irrefl x (hDD x hx x hxB))
  set tm := Dm.max' hm with htm
  set tp := Dp.min' hp with htp
  have hsub : ∀ {Em Ep : Finset ℕ}, Em ⊆ Dm → Ep ⊆ Dp →
      ((Em ∪ Ep) ∩ Dm = Em ∧ (Em ∪ Ep) ∩ Dp = Ep) := by
    intro Em Ep h1 h2
    constructor
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (Finset.disjoint_right.mp hdisj (h2 h))
      · intro h
        exact ⟨Or.inl h, h1 h⟩
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd hx (Finset.disjoint_left.mp hdisj (h1 h))
        · exact h
      · intro h
        exact ⟨Or.inr h, h2 h⟩
  unfold Zsum
  rw [sum_powerset_union hdisj,
    Finset.sum_product' (Dm.powerset) (Dp.powerset)
      (fun Em Ep => if (((Em ∪ Ep) ∩ Dm).card : ℤ) = i ∧ (((Em ∪ Ep) ∩ Dp).card : ℤ) = j
        then bondWeight ψ (Dm ∪ Dp) (Em ∪ Ep) else 0)]
  -- right-hand side as a double sum
  show _ = (if tm + 1 = tp then ψ else 1)
      * ((∑ E ∈ Dm.powerset, if (E.card : ℤ) = i ∧ tm ∉ E then bondWeight ψ Dm E else 0)
          * (∑ E ∈ Dp.powerset, if (E.card : ℤ) = j ∧ tp ∉ E then bondWeight ψ Dp E else 0)
        + (∑ E ∈ Dm.powerset, if (E.card : ℤ) = i ∧ tm ∈ E then bondWeight ψ Dm E else 0)
          * (∑ E ∈ Dp.powerset, if (E.card : ℤ) = j ∧ tp ∈ E then bondWeight ψ Dp E else 0))
      + (∑ E ∈ Dm.powerset, if (E.card : ℤ) = i ∧ tm ∉ E then bondWeight ψ Dm E else 0)
        * (∑ E ∈ Dp.powerset, if (E.card : ℤ) = j ∧ tp ∈ E then bondWeight ψ Dp E else 0)
      + (∑ E ∈ Dm.powerset, if (E.card : ℤ) = i ∧ tm ∈ E then bondWeight ψ Dm E else 0)
        * (∑ E ∈ Dp.powerset, if (E.card : ℤ) = j ∧ tp ∉ E then bondWeight ψ Dp E else 0)
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Em hEm
  apply Finset.sum_congr rfl
  intro Ep hEp
  rw [Finset.mem_powerset] at hEm hEp
  obtain ⟨hi, hj⟩ := hsub hEm hEp
  rw [hi, hj, bondWeight_split ψ hm hp hDD (Em ∪ Ep)]
  have c1 : bondWeight ψ Dm (Em ∪ Ep) = bondWeight ψ Dm Em := by
    apply bondWeight_congr
    intro x hx
    rw [Finset.mem_union]
    exact ⟨fun h => h.resolve_right (fun h' => Finset.disjoint_left.mp hdisj hx (hEp h')),
      fun h => Or.inl h⟩
  have c2 : bondWeight ψ Dp (Em ∪ Ep) = bondWeight ψ Dp Ep := by
    apply bondWeight_congr
    intro x hx
    rw [Finset.mem_union]
    exact ⟨fun h => h.resolve_left (fun h' => Finset.disjoint_right.mp hdisj hx (hEm h')),
      fun h => Or.inr h⟩
  have ntm : tm ∈ Dm := Finset.max'_mem Dm hm
  have ntp : tp ∈ Dp := Finset.min'_mem Dp hp
  have e1 : tm ∈ Em ∪ Ep ↔ tm ∈ Em := by
    rw [Finset.mem_union]
    exact ⟨fun h => h.resolve_right (fun h' => Finset.disjoint_left.mp hdisj ntm (hEp h')),
      fun h => Or.inl h⟩
  have e2 : tp ∈ Em ∪ Ep ↔ tp ∈ Ep := by
    rw [Finset.mem_union]
    exact ⟨fun h => h.resolve_left (fun h' => Finset.disjoint_right.mp hdisj ntp (hEm h')),
      fun h => Or.inr h⟩
  rw [c1, c2]
  simp only [← htm, ← htp, e1, e2]
  by_cases a : (Em.card : ℤ) = i <;> by_cases b : (Ep.card : ℤ) = j <;>
    by_cases c : tm ∈ Em <;> by_cases d : tp ∈ Ep <;> by_cases f : tm + 1 = tp <;>
    simp [a, b, c, d, f] <;> ring

end CommonTime
