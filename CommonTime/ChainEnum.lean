import CommonTime.Chain

/-!
# Enumeration of a coupled binary chain equals its recursion (Theorem 4.7, step 1)

For a finite set of sites `D ⊆ ℕ` and `E ⊆ D` (the sites carrying a `1`), the
bond weight is

  `bondWeight ψ D E = ∏_{u, j ∈ D, u + 1 = j} ψ^{1{(u ∈ E) ↔ (j ∈ E)}}`,

the weight `∏ φᵤ^{1{ηᵤ = ηᵤ₊₁}}` of the manuscript with coupling `ψ` between
adjacent integers and `1` across gaps. Classifying `E` by its cardinality and
by whether a designated site `t` lies in `E` gives a `ChainState`
(`enumState ψ D t`). This file proves that, for `t` the largest element of
`D` (`enum_isChain_max`) or the smallest (`enum_isChain_min`), this state is
produced by the chain recursion of `Chain.lean` with couplings in `{1, ψ}`,
so every conclusion of that file applies to it when `1 ≤ ψ ≤ 2`.

`IsChain A N` records that `A` arises from `chainOne` by `N - 1` steps with
couplings in `[1, 2]`; `Zdiff_nonneg_isChain` restates the cut-difference
inequality in those terms.
-/

namespace CommonTime

attribute [ext] ChainState

/-! ## Chains described by a predicate -/

/-- `A` is obtained from the one-site chain by steps with couplings in `[1, 2]`,
    and has `N` sites. -/
inductive IsChain : ChainState → ℤ → Prop
  | one : IsChain chainOne 1
  | step {A : ChainState} {N : ℤ} (φ : ℝ) (h1 : 1 ≤ φ) (h2 : φ ≤ 2) :
      IsChain A N → IsChain (chainStep φ A) (N + 1)

theorem IsChain.exists_list {A : ChainState} {N : ℤ} (h : IsChain A N) :
    ∃ l : List ℝ, Couplings l ∧ A = chain l ∧ N = sites l := by
  induction h with
  | one =>
    refine ⟨[], ?_, rfl, sites_nil.symm⟩
    intro φ hφ
    exact absurd hφ (List.not_mem_nil)
  | step φ h1 h2 _ ih =>
    obtain ⟨l, hl, rfl, rfl⟩ := ih
    refine ⟨φ :: l, ?_, rfl, (sites_cons φ l).symm⟩
    intro ψ hψ
    rw [List.mem_cons] at hψ
    rcases hψ with rfl | hψ
    · exact ⟨h1, h2⟩
    · exact hl ψ hψ

/-- The cut-difference inequality for chains given by `IsChain`. -/
theorem Zdiff_nonneg_isChain {A B : ChainState} {NA NB : ℤ}
    (hA : IsChain A NA) (hB : IsChain B NB) {κ : ℝ} (hκ : 1 ≤ κ) (ip jp jm : ℤ)
    (hi : NA - ip < ip) (hj : jp < jm) (hjs : NB + 1 ≤ jp + jm) :
    Zpair κ A B (NA - ip) jm ≤ Zpair κ A B ip jp := by
  obtain ⟨lA, hlA, rfl, rfl⟩ := hA.exists_list
  obtain ⟨lB, hlB, rfl, rfl⟩ := hB.exists_list
  exact Zdiff_nonneg hlA hlB hκ ip jp jm hi hj hjs

/-! ## Bond weights -/

/-- The weight of the bond `(u, u+1)`: `ψ` if both sites carry the same bit. -/
def bondFactor (ψ : ℝ) (E : Finset ℕ) (u j : ℕ) : ℝ :=
  if u + 1 = j ∧ (u ∈ E ↔ j ∈ E) then ψ else 1

/-- Product of the bond weights over all bonds inside `D`. -/
def bondWeight (ψ : ℝ) (D E : Finset ℕ) : ℝ :=
  ∏ u ∈ D, ∏ j ∈ D, bondFactor ψ E u j

theorem bondFactor_self (ψ : ℝ) (E : Finset ℕ) (m : ℕ) : bondFactor ψ E m m = 1 := by
  unfold bondFactor
  exact ite_eq_right (fun h => by omega)

theorem bondFactor_congr (ψ : ℝ) {E E' : Finset ℕ} {u j : ℕ}
    (hu : u ∈ E ↔ u ∈ E') (hj : j ∈ E ↔ j ∈ E') :
    bondFactor ψ E u j = bondFactor ψ E' u j := by
  unfold bondFactor
  simp only [hu, hj]

/-- The bond weight depends on `E` only through `E ∩ D`. -/
theorem bondWeight_congr (ψ : ℝ) {D E E' : Finset ℕ}
    (h : ∀ x ∈ D, (x ∈ E ↔ x ∈ E')) : bondWeight ψ D E = bondWeight ψ D E' := by
  unfold bondWeight
  apply Finset.prod_congr rfl
  intro u hu
  apply Finset.prod_congr rfl
  intro j hj
  exact bondFactor_congr ψ (h u hu) (h j hj)

theorem bondWeight_insert (ψ : ℝ) {D : Finset ℕ} {m : ℕ} (hm : m ∉ D) (E : Finset ℕ) :
    bondWeight ψ (insert m D) E
      = bondWeight ψ D E * ((∏ j ∈ D, bondFactor ψ E m j) * ∏ u ∈ D, bondFactor ψ E u m) := by
  unfold bondWeight
  rw [Finset.prod_insert hm, Finset.prod_insert hm, bondFactor_self]
  have e : ∀ u ∈ D, ∏ j ∈ insert m D, bondFactor ψ E u j
      = bondFactor ψ E u m * ∏ j ∈ D, bondFactor ψ E u j := by
    intro u _
    rw [Finset.prod_insert hm]
  rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib]
  ring

/-- No bond from a new site above all of `D` goes upward. -/
theorem prod_bondFactor_above (ψ : ℝ) (E : Finset ℕ) {D : Finset ℕ} {m : ℕ}
    (hm : ∀ x ∈ D, x < m) : ∏ j ∈ D, bondFactor ψ E m j = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  unfold bondFactor
  exact ite_eq_right (fun h => by have := hm j hj; omega)

/-- No bond from a new site below all of `D` goes downward. -/
theorem prod_bondFactor_below (ψ : ℝ) (E : Finset ℕ) {D : Finset ℕ} {m : ℕ}
    (hm : ∀ x ∈ D, m < x) : ∏ u ∈ D, bondFactor ψ E u m = 1 := by
  apply Finset.prod_eq_one
  intro u hu
  unfold bondFactor
  exact ite_eq_right (fun h => by have := hm u hu; omega)

/-- The only possible bond from a new top site `m` goes to the old top `t`. -/
theorem prod_bondFactor_top (ψ : ℝ) (E : Finset ℕ) {D : Finset ℕ} {t m : ℕ}
    (ht : t ∈ D) (htmax : ∀ x ∈ D, x ≤ t) (htm : t < m) :
    ∏ u ∈ D, bondFactor ψ E u m = if t + 1 = m ∧ (t ∈ E ↔ m ∈ E) then ψ else 1 := by
  rw [Finset.prod_eq_single_of_mem t ht]
  · rfl
  · intro u hu hut
    unfold bondFactor
    exact ite_eq_right (fun h => by have := htmax u hu; omega)

/-- The only possible bond from a new bottom site `m` goes to the old bottom `t`. -/
theorem prod_bondFactor_bottom (ψ : ℝ) (E : Finset ℕ) {D : Finset ℕ} {t m : ℕ}
    (ht : t ∈ D) (htmin : ∀ x ∈ D, t ≤ x) (hmt : m < t) :
    ∏ j ∈ D, bondFactor ψ E m j = if m + 1 = t ∧ (m ∈ E ↔ t ∈ E) then ψ else 1 := by
  rw [Finset.prod_eq_single_of_mem t ht]
  · rfl
  · intro j hj hjt
    unfold bondFactor
    exact ite_eq_right (fun h => by have := htmin j hj; omega)

/-! ## The enumeration state -/

/-- `A₀(i)`: total bond weight of `E ⊆ D` with `|E| = i` and `t ∉ E`;
    `A₁(i)`: the same with `t ∈ E`. -/
def enumState (ψ : ℝ) (D : Finset ℕ) (t : ℕ) : ChainState :=
  ⟨fun i => ∑ E ∈ D.powerset, if (E.card : ℤ) = i ∧ t ∉ E then bondWeight ψ D E else 0,
   fun i => ∑ E ∈ D.powerset, if (E.card : ℤ) = i ∧ t ∈ E then bondWeight ψ D E else 0⟩

theorem bondWeight_singleton (ψ : ℝ) (t : ℕ) (E : Finset ℕ) : bondWeight ψ {t} E = 1 := by
  unfold bondWeight
  rw [Finset.prod_singleton, Finset.prod_singleton, bondFactor_self]

theorem enumState_singleton (ψ : ℝ) (t : ℕ) : enumState ψ {t} t = chainOne := by
  have hne : (∅ : Finset ℕ) ≠ {t} := by
    intro h
    have : t ∈ (∅ : Finset ℕ) := by
      rw [h]
      exact Finset.mem_singleton_self t
    exact Finset.notMem_empty t this
  have hpow : ({t} : Finset ℕ).powerset = {∅, {t}} := by
    ext E
    simp [Finset.subset_singleton_iff]
  ext i
  · show (∑ E ∈ ({t} : Finset ℕ).powerset,
        if (E.card : ℤ) = i ∧ t ∉ E then bondWeight ψ {t} E else 0) = if i = 0 then 1 else 0
    rw [hpow, Finset.sum_pair hne, bondWeight_singleton, bondWeight_singleton,
      Finset.card_empty, Finset.card_singleton]
    have h1 : ¬ (((1 : ℕ) : ℤ) = i ∧ t ∉ ({t} : Finset ℕ)) :=
      fun h => h.2 (Finset.mem_singleton_self t)
    rw [ite_eq_right h1, add_zero]
    by_cases h0 : i = 0
    · rw [ite_eq_left h0, ite_eq_left ⟨by simp [h0], Finset.notMem_empty t⟩]
    · rw [ite_eq_right h0, ite_eq_right (fun h => h0 (by have := h.1; omega))]
  · show (∑ E ∈ ({t} : Finset ℕ).powerset,
        if (E.card : ℤ) = i ∧ t ∈ E then bondWeight ψ {t} E else 0) = if i = 1 then 1 else 0
    rw [hpow, Finset.sum_pair hne, bondWeight_singleton, bondWeight_singleton,
      Finset.card_empty, Finset.card_singleton]
    have h0 : ¬ (((0 : ℕ) : ℤ) = i ∧ t ∈ (∅ : Finset ℕ)) :=
      fun h => Finset.notMem_empty t h.2
    rw [ite_eq_right h0, zero_add]
    by_cases h1 : i = 1
    · rw [ite_eq_left h1, ite_eq_left ⟨by simp [h1], Finset.mem_singleton_self t⟩]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (by have := h.1; omega))]

/-- Splitting a sum over `(insert m D).powerset` into subsets avoiding and
    containing `m`. -/
theorem sum_powerset_insert {m : ℕ} {D : Finset ℕ} (hm : m ∉ D) (f : Finset ℕ → ℝ) :
    ∑ E ∈ (insert m D).powerset, f E
      = ∑ E ∈ D.powerset, f E + ∑ E ∈ D.powerset, f (insert m E) := by
  rw [Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
  · intro E₁ h₁ E₂ h₂ h
    have hm₁ : m ∉ E₁ := fun h' => hm (Finset.mem_powerset.mp h₁ h')
    have hm₂ : m ∉ E₂ := fun h' => hm (Finset.mem_powerset.mp h₂ h')
    rw [← Finset.erase_insert hm₁, ← Finset.erase_insert hm₂, h]
  · rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_image] at hE'
    obtain ⟨E', _, rfl⟩ := hE'
    exact hm (Finset.mem_powerset.mp hE (Finset.mem_insert_self m E'))

/-- Adding a new largest site `m` to `D` with top `t` is one chain step with
    coupling `ψ` if `t + 1 = m` and `1` otherwise. -/
theorem enumState_insert_max (ψ : ℝ) {D : Finset ℕ} {t m : ℕ}
    (ht : t ∈ D) (htmax : ∀ x ∈ D, x ≤ t) (hm : ∀ x ∈ D, x < m) :
    enumState ψ (insert m D) m
      = chainStep (if t + 1 = m then ψ else 1) (enumState ψ D t) := by
  have hmD : m ∉ D := fun h => lt_irrefl m (hm m h)
  have htm : t < m := hm t ht
  -- weights of the two kinds of subsets of `insert m D`
  have w0 : ∀ E ∈ D.powerset, bondWeight ψ (insert m D) E
      = bondWeight ψ D E * (if t + 1 = m ∧ t ∉ E then ψ else 1) := by
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    rw [bondWeight_insert ψ hmD E, prod_bondFactor_above ψ E hm, one_mul,
      prod_bondFactor_top ψ E ht htmax htm]
    congr 1
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => hmE (h2.mp h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨fun h => absurd h h2, fun h => absurd h hmE⟩⟩
  have w1 : ∀ E ∈ D.powerset, bondWeight ψ (insert m D) (insert m E)
      = bondWeight ψ D E * (if t + 1 = m ∧ t ∈ E then ψ else 1) := by
    intro E hE
    have htm' : t ≠ m := ne_of_lt htm
    rw [bondWeight_insert ψ hmD, prod_bondFactor_above ψ _ hm, one_mul,
      prod_bondFactor_top ψ _ ht htmax htm]
    have hc : bondWeight ψ D (insert m E) = bondWeight ψ D E := by
      apply bondWeight_congr
      intro x hx
      have hxm : x ≠ m := ne_of_lt (hm x hx)
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left hxm, fun h => Or.inr h⟩
    rw [hc]
    congr 1
    apply if_congr _ rfl rfl
    have e1 : t ∈ insert m E ↔ t ∈ E := by
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left htm', fun h => Or.inr h⟩
    have e2 : m ∈ insert m E := Finset.mem_insert_self m E
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, e1.mp (h2.mpr e2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨fun _ => e2, fun _ => e1.mpr h2⟩⟩
  have hcard : ∀ E ∈ D.powerset, ((insert m E).card : ℤ) = (E.card : ℤ) + 1 := by
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    rw [Finset.card_insert_of_notMem hmE]
    push_cast
    rfl
  ext i
  · show (∑ E ∈ (insert m D).powerset,
        if (E.card : ℤ) = i ∧ m ∉ E then bondWeight ψ (insert m D) E else 0)
      = (if t + 1 = m then ψ else 1)
          * (∑ E ∈ D.powerset, if (E.card : ℤ) = i ∧ t ∉ E then bondWeight ψ D E else 0)
        + ∑ E ∈ D.powerset, if (E.card : ℤ) = i ∧ t ∈ E then bondWeight ψ D E else 0
    rw [sum_powerset_insert hmD, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    have hmE' : m ∈ insert m E := Finset.mem_insert_self m E
    rw [ite_eq_right (fun h : ((insert m E).card : ℤ) = i ∧ m ∉ insert m E => h.2 hmE'),
      add_zero, w0 E hE]
    by_cases hi : (E.card : ℤ) = i
    · rw [ite_eq_left ⟨hi, hmE⟩]
      by_cases hadj : t + 1 = m
      · rw [ite_eq_left hadj]
        by_cases htE : t ∈ E
        · rw [ite_eq_right (fun h => h.2 htE), ite_eq_right (fun h => h.2 htE),
            ite_eq_left ⟨hi, htE⟩]
          ring
        · rw [ite_eq_left ⟨hadj, htE⟩, ite_eq_left ⟨hi, htE⟩,
            ite_eq_right (fun h => htE h.2)]
          ring
      · simp only [hadj, false_and, ↓reduceIte]
        by_cases htE : t ∈ E
        · rw [ite_eq_right (fun h => h.2 htE), ite_eq_left ⟨hi, htE⟩]
          ring
        · rw [ite_eq_left ⟨hi, htE⟩, ite_eq_right (fun h => htE h.2)]
          ring
    · simp only [hi, false_and, ↓reduceIte]
      ring
  · show (∑ E ∈ (insert m D).powerset,
        if (E.card : ℤ) = i ∧ m ∈ E then bondWeight ψ (insert m D) E else 0)
      = (∑ E ∈ D.powerset, if (E.card : ℤ) = i - 1 ∧ t ∉ E then bondWeight ψ D E else 0)
        + (if t + 1 = m then ψ else 1)
          * ∑ E ∈ D.powerset, if (E.card : ℤ) = i - 1 ∧ t ∈ E then bondWeight ψ D E else 0
    rw [sum_powerset_insert hmD, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    have hmE' : m ∈ insert m E := Finset.mem_insert_self m E
    rw [ite_eq_right (fun h : (E.card : ℤ) = i ∧ m ∈ E => hmE h.2), zero_add, w1 E hE,
      hcard E hE]
    by_cases hi : (E.card : ℤ) + 1 = i
    · rw [ite_eq_left ⟨hi, hmE'⟩]
      have hi' : (E.card : ℤ) = i - 1 := by omega
      by_cases hadj : t + 1 = m
      · rw [ite_eq_left hadj]
        by_cases htE : t ∈ E
        · rw [ite_eq_left ⟨hadj, htE⟩, ite_eq_right (fun h => h.2 htE),
            ite_eq_left ⟨hi', htE⟩]
          ring
        · rw [ite_eq_right (fun h => htE h.2), ite_eq_left ⟨hi', htE⟩,
            ite_eq_right (fun h => htE h.2)]
          ring
      · simp only [hadj, false_and, ↓reduceIte]
        by_cases htE : t ∈ E
        · rw [ite_eq_right (fun h => h.2 htE), ite_eq_left ⟨hi', htE⟩]
          ring
        · rw [ite_eq_left ⟨hi', htE⟩, ite_eq_right (fun h => htE h.2)]
          ring
    · have hi' : ¬ (E.card : ℤ) = i - 1 := fun h => hi (by omega)
      simp only [hi, hi', false_and, ↓reduceIte]
      ring

/-- Adding a new smallest site `m` to `D` with bottom `t` is one chain step
    with coupling `ψ` if `m + 1 = t` and `1` otherwise. -/
theorem enumState_insert_min (ψ : ℝ) {D : Finset ℕ} {t m : ℕ}
    (ht : t ∈ D) (htmin : ∀ x ∈ D, t ≤ x) (hm : ∀ x ∈ D, m < x) :
    enumState ψ (insert m D) m
      = chainStep (if m + 1 = t then ψ else 1) (enumState ψ D t) := by
  have hmD : m ∉ D := fun h => lt_irrefl m (hm m h)
  have hmt : m < t := hm t ht
  have w0 : ∀ E ∈ D.powerset, bondWeight ψ (insert m D) E
      = bondWeight ψ D E * (if m + 1 = t ∧ t ∉ E then ψ else 1) := by
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    rw [bondWeight_insert ψ hmD E, prod_bondFactor_below ψ E hm, mul_one,
      prod_bondFactor_bottom ψ E ht htmin hmt]
    congr 1
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => hmE (h2.mpr h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨fun h => absurd h hmE, fun h => absurd h h2⟩⟩
  have w1 : ∀ E ∈ D.powerset, bondWeight ψ (insert m D) (insert m E)
      = bondWeight ψ D E * (if m + 1 = t ∧ t ∈ E then ψ else 1) := by
    intro E hE
    have hmt' : t ≠ m := ne_of_gt hmt
    rw [bondWeight_insert ψ hmD, prod_bondFactor_below ψ _ hm, mul_one,
      prod_bondFactor_bottom ψ _ ht htmin hmt]
    have hc : bondWeight ψ D (insert m E) = bondWeight ψ D E := by
      apply bondWeight_congr
      intro x hx
      have hxm : x ≠ m := ne_of_gt (hm x hx)
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left hxm, fun h => Or.inr h⟩
    rw [hc]
    congr 1
    apply if_congr _ rfl rfl
    have e1 : t ∈ insert m E ↔ t ∈ E := by
      rw [Finset.mem_insert]
      exact ⟨fun h => h.resolve_left hmt', fun h => Or.inr h⟩
    have e2 : m ∈ insert m E := Finset.mem_insert_self m E
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, e1.mp (h2.mp e2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨fun _ => e1.mpr h2, fun _ => e2⟩⟩
  have hcard : ∀ E ∈ D.powerset, ((insert m E).card : ℤ) = (E.card : ℤ) + 1 := by
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    rw [Finset.card_insert_of_notMem hmE]
    push_cast
    rfl
  ext i
  · show (∑ E ∈ (insert m D).powerset,
        if (E.card : ℤ) = i ∧ m ∉ E then bondWeight ψ (insert m D) E else 0)
      = (if m + 1 = t then ψ else 1)
          * (∑ E ∈ D.powerset, if (E.card : ℤ) = i ∧ t ∉ E then bondWeight ψ D E else 0)
        + ∑ E ∈ D.powerset, if (E.card : ℤ) = i ∧ t ∈ E then bondWeight ψ D E else 0
    rw [sum_powerset_insert hmD, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    have hmE' : m ∈ insert m E := Finset.mem_insert_self m E
    rw [ite_eq_right (fun h : ((insert m E).card : ℤ) = i ∧ m ∉ insert m E => h.2 hmE'),
      add_zero, w0 E hE]
    by_cases hi : (E.card : ℤ) = i
    · rw [ite_eq_left ⟨hi, hmE⟩]
      by_cases hadj : m + 1 = t
      · rw [ite_eq_left hadj]
        by_cases htE : t ∈ E
        · rw [ite_eq_right (fun h => h.2 htE), ite_eq_right (fun h => h.2 htE),
            ite_eq_left ⟨hi, htE⟩]
          ring
        · rw [ite_eq_left ⟨hadj, htE⟩, ite_eq_left ⟨hi, htE⟩,
            ite_eq_right (fun h => htE h.2)]
          ring
      · simp only [hadj, false_and, ↓reduceIte]
        by_cases htE : t ∈ E
        · rw [ite_eq_right (fun h => h.2 htE), ite_eq_left ⟨hi, htE⟩]
          ring
        · rw [ite_eq_left ⟨hi, htE⟩, ite_eq_right (fun h => htE h.2)]
          ring
    · simp only [hi, false_and, ↓reduceIte]
      ring
  · show (∑ E ∈ (insert m D).powerset,
        if (E.card : ℤ) = i ∧ m ∈ E then bondWeight ψ (insert m D) E else 0)
      = (∑ E ∈ D.powerset, if (E.card : ℤ) = i - 1 ∧ t ∉ E then bondWeight ψ D E else 0)
        + (if m + 1 = t then ψ else 1)
          * ∑ E ∈ D.powerset, if (E.card : ℤ) = i - 1 ∧ t ∈ E then bondWeight ψ D E else 0
    rw [sum_powerset_insert hmD, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    have hmE : m ∉ E := fun h => hmD (Finset.mem_powerset.mp hE h)
    have hmE' : m ∈ insert m E := Finset.mem_insert_self m E
    rw [ite_eq_right (fun h : (E.card : ℤ) = i ∧ m ∈ E => hmE h.2), zero_add, w1 E hE,
      hcard E hE]
    by_cases hi : (E.card : ℤ) + 1 = i
    · rw [ite_eq_left ⟨hi, hmE'⟩]
      have hi' : (E.card : ℤ) = i - 1 := by omega
      by_cases hadj : m + 1 = t
      · rw [ite_eq_left hadj]
        by_cases htE : t ∈ E
        · rw [ite_eq_left ⟨hadj, htE⟩, ite_eq_right (fun h => h.2 htE),
            ite_eq_left ⟨hi', htE⟩]
          ring
        · rw [ite_eq_right (fun h => htE h.2), ite_eq_left ⟨hi', htE⟩,
            ite_eq_right (fun h => htE h.2)]
          ring
      · simp only [hadj, false_and, ↓reduceIte]
        by_cases htE : t ∈ E
        · rw [ite_eq_right (fun h => h.2 htE), ite_eq_left ⟨hi', htE⟩]
          ring
        · rw [ite_eq_left ⟨hi', htE⟩, ite_eq_right (fun h => htE h.2)]
          ring
    · have hi' : ¬ (E.card : ℤ) = i - 1 := fun h => hi (by omega)
      simp only [hi, hi', false_and, ↓reduceIte]
      ring

/-! ## The enumeration is a chain -/

theorem coupling_mem {ψ : ℝ} (h1 : 1 ≤ ψ) (h2 : ψ ≤ 2) (c : Prop) [Decidable c] :
    1 ≤ (if c then ψ else 1) ∧ (if c then ψ else 1) ≤ 2 := by
  split_ifs
  · exact ⟨h1, h2⟩
  · exact ⟨le_refl 1, by norm_num⟩

theorem max'_insert_of_lt {D : Finset ℕ} {a : ℕ} (hD : D.Nonempty) (ha : ∀ x ∈ D, x < a)
    (h : (insert a D).Nonempty) : (insert a D).max' h = a := by
  apply le_antisymm
  · have hmem := Finset.max'_mem (insert a D) h
    rw [Finset.mem_insert] at hmem
    rcases hmem with hm | hm
    · exact le_of_eq hm
    · exact le_of_lt (ha _ hm)
  · exact Finset.le_max' (insert a D) a (Finset.mem_insert_self a D)

theorem min'_insert_of_lt {D : Finset ℕ} {a : ℕ} (hD : D.Nonempty) (ha : ∀ x ∈ D, a < x)
    (h : (insert a D).Nonempty) : (insert a D).min' h = a := by
  apply le_antisymm
  · exact Finset.min'_le (insert a D) a (Finset.mem_insert_self a D)
  · have hmem := Finset.min'_mem (insert a D) h
    rw [Finset.mem_insert] at hmem
    rcases hmem with hm | hm
    · exact le_of_eq hm.symm
    · exact le_of_lt (ha _ hm)

/-- Scanning the sites of `D` upward: the enumeration with the top site
    designated is a chain with `|D|` sites. -/
theorem enum_isChain_max {ψ : ℝ} (h1 : 1 ≤ ψ) (h2 : ψ ≤ 2) (D : Finset ℕ) :
    ∀ hD : D.Nonempty, IsChain (enumState ψ D (D.max' hD)) (D.card : ℤ) := by
  induction D using Finset.induction_on_max with
  | empty =>
    intro hD
    exact absurd hD Finset.not_nonempty_empty
  | insert a s ha ih =>
    intro hD
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      have e : (insert a (∅ : Finset ℕ)).max' hD = a := by
        apply le_antisymm
        · have hmem := Finset.max'_mem (insert a ∅) hD
          rw [Finset.mem_insert] at hmem
          rcases hmem with hm | hm
          · exact le_of_eq hm
          · exact absurd hm (Finset.notMem_empty _)
        · exact Finset.le_max' _ a (Finset.mem_insert_self a ∅)
      rw [e, Finset.insert_empty, enumState_singleton, Finset.card_singleton]
      exact IsChain.one
    · have haS : a ∉ s := fun h => lt_irrefl a (ha a h)
      rw [max'_insert_of_lt hs ha hD, Finset.card_insert_of_notMem haS,
        enumState_insert_max ψ (Finset.max'_mem s hs) (fun x hx => Finset.le_max' s x hx) ha]
      push_cast
      exact IsChain.step _ (coupling_mem h1 h2 _).1 (coupling_mem h1 h2 _).2 (ih hs)

/-- Scanning the sites of `D` downward: the enumeration with the bottom site
    designated is a chain with `|D|` sites. -/
theorem enum_isChain_min {ψ : ℝ} (h1 : 1 ≤ ψ) (h2 : ψ ≤ 2) (D : Finset ℕ) :
    ∀ hD : D.Nonempty, IsChain (enumState ψ D (D.min' hD)) (D.card : ℤ) := by
  induction D using Finset.induction_on_min with
  | empty =>
    intro hD
    exact absurd hD Finset.not_nonempty_empty
  | insert a s ha ih =>
    intro hD
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      have e : (insert a (∅ : Finset ℕ)).min' hD = a := by
        apply le_antisymm
        · exact Finset.min'_le _ a (Finset.mem_insert_self a ∅)
        · have hmem := Finset.min'_mem (insert a ∅) hD
          rw [Finset.mem_insert] at hmem
          rcases hmem with hm | hm
          · exact le_of_eq hm.symm
          · exact absurd hm (Finset.notMem_empty _)
      rw [e, Finset.insert_empty, enumState_singleton, Finset.card_singleton]
      exact IsChain.one
    · have haS : a ∉ s := fun h => lt_irrefl a (ha a h)
      rw [min'_insert_of_lt hs ha hD, Finset.card_insert_of_notMem haS,
        enumState_insert_min ψ (Finset.min'_mem s hs) (fun x hx => Finset.min'_le s x hx) ha]
      push_cast
      exact IsChain.step _ (coupling_mem h1 h2 _).1 (coupling_mem h1 h2 _).2 (ih hs)

end CommonTime