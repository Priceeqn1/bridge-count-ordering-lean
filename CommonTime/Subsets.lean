import CommonTime.Prefix

/-!
# Paths as vertex sets (Theorem 4.7, steps 2–3)

An admissible `m`-jump path `0 → k` is determined by its vertex set
`V = {p 0, …, p m}`, a subset of `{0, …, k}` of cardinality `m + 1`
containing both endpoints. This file:

1. defines the Toeplitz step kernel `b₁ = 1`, `b_d = θ (d ≥ 2)` of
   display (28) (`stepKernel`);
2. expresses the weight of a path under that kernel through its vertex set
   (`pathWeight_eq_subWeight`): the kernel factor is `θ` for every vertex of
   `V ∖ {0}` whose predecessor is not in `V`, and the activity factor is the
   product of the activities of `V ∖ {k}`;
3. expresses the prefix visit count through the vertex set
   (`prefixVisits_eq_prefixCount`);
4. rewrites the prefix count array as a sum over vertex sets
   (`prefixArray_stepKernel`), through the bijection
   `paths k m ≃ vertexSets k m` given by `Finset.orderEmbOfFin`.

Nothing here is specific to the parameter range of Theorem 4.7.
-/

namespace CommonTime

variable {k : ℕ}

/-! ## The step kernel -/

/-- Toeplitz step kernel: a jump of size `1` has weight `1`, every larger
    jump has weight `θ`; zero on and above the diagonal. -/
noncomputable def stepKernel (k : ℕ) (θ : ℝ) : Vertex k → Vertex k → ℝ :=
  fun n j => if j < n then (if n.val = j.val + 1 then 1 else θ) else 0

theorem stepKernel_tri (θ : ℝ) : StrictLowerTriangular (stepKernel k θ) := by
  intro n j h
  unfold stepKernel
  exact ite_eq_right (not_lt_of_ge h)

theorem stepKernel_pos {θ : ℝ} (hθ : 0 < θ) : PositiveAdmissible (stepKernel k θ) := by
  intro n j h
  unfold stepKernel
  rw [ite_eq_left h]
  split_ifs
  · exact one_pos
  · exact hθ

/-! ## Vertex sets -/

/-- The vertex set of a path. -/
def vertexSet {m : ℕ} (p : Path k m) : Finset (Vertex k) := Finset.univ.image p

/-- Vertex sets of admissible `m`-jump paths `0 → k`. -/
def vertexSets (k m : ℕ) : Finset (Finset (Vertex k)) :=
  (Finset.univ : Finset (Vertex k)).powerset.filter
    (fun V => (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ V ∧
      (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ V ∧ V.card = m + 1)

/-- `j - 1 ∈ V`. -/
def hasPred (V : Finset (Vertex k)) (j : Vertex k) : Prop := ∃ u ∈ V, u.val + 1 = j.val

instance (V : Finset (Vertex k)) (j : Vertex k) : Decidable (hasPred V j) := by
  unfold hasPred
  infer_instance

/-- The weight of the path with vertex set `V` under the step kernel. -/
noncomputable def subWeight (k : ℕ) (θ : ℝ) (V : Finset (Vertex k)) : Poly k :=
  MvPolynomial.C (∏ j ∈ V.erase ⟨0, Nat.zero_lt_succ k⟩, (if hasPred V j then 1 else θ))
    * ∏ v ∈ V.erase ⟨k, Nat.lt_succ_self k⟩, activity v

/-- Number of vertices of `V` in `[1, q]`. -/
def prefixCount (q : ℕ) (V : Finset (Vertex k)) : ℕ :=
  (V.filter (fun v => 0 < v.val ∧ v.val ≤ q)).card

theorem mem_paths {m : ℕ} {p : Path k m} : p ∈ paths k m ↔ admissible k m p := by
  unfold paths
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem admissible_strictMono {m : ℕ} {p : Path k m} (hp : admissible k m p) : StrictMono p :=
  admissibleTo_strictMono (z := ⟨k, Nat.lt_succ_self k⟩) hp

theorem mem_vertexSets {m : ℕ} {V : Finset (Vertex k)} :
    V ∈ vertexSets k m ↔ (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ V ∧
      (⟨k, Nat.lt_succ_self k⟩ : Vertex k) ∈ V ∧ V.card = m + 1 := by
  unfold vertexSets
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Finset.mem_powerset.mpr (Finset.subset_univ V), h⟩

theorem vertexSet_mem {m : ℕ} {p : Path k m} (hp : admissible k m p) :
    vertexSet p ∈ vertexSets k m := by
  rw [mem_vertexSets]
  unfold vertexSet
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.mem_image]
    exact ⟨⟨0, Nat.zero_lt_succ m⟩, Finset.mem_univ _, hp.1⟩
  · rw [Finset.mem_image]
    exact ⟨⟨m, Nat.lt_succ_self m⟩, Finset.mem_univ _, hp.2.1⟩
  · rw [Finset.card_image_of_injective _ (admissible_strictMono hp).injective,
      Finset.card_univ, Fintype.card_fin]

/-! ## Reindexing the jumps by their lower and upper vertices -/

theorem image_castSucc {m : ℕ} {p : Path k m} (hp : admissible k m p) :
    Finset.univ.image (fun i : Fin m => p (Fin.castSucc i))
      = (vertexSet p).erase ⟨k, Nat.lt_succ_self k⟩ := by
  have hmono := admissible_strictMono hp
  have hlast : p (Fin.last m) = ⟨k, Nat.lt_succ_self k⟩ := hp.2.1
  ext v
  rw [Finset.mem_image, Finset.mem_erase, vertexSet, Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    refine ⟨?_, Fin.castSucc i, Finset.mem_univ _, rfl⟩
    intro h
    have h1 : p (Fin.castSucc i) < p (Fin.last m) := hmono (Fin.castSucc_lt_last i)
    rw [h, hlast] at h1
    exact lt_irrefl _ h1
  · rintro ⟨hv, i, -, rfl⟩
    have hi : i.val < m := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with h | h
      · exact h
      · exfalso
        apply hv
        rw [← hlast]
        congr 1
        exact Fin.ext h
    exact ⟨⟨i.val, hi⟩, Finset.mem_univ _, rfl⟩

theorem image_succ {m : ℕ} {p : Path k m} (hp : admissible k m p) :
    Finset.univ.image (fun i : Fin m => p (Fin.succ i))
      = (vertexSet p).erase ⟨0, Nat.zero_lt_succ k⟩ := by
  have hmono := admissible_strictMono hp
  have hzero : p (0 : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ k⟩ := hp.1
  ext v
  rw [Finset.mem_image, Finset.mem_erase, vertexSet, Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    refine ⟨?_, Fin.succ i, Finset.mem_univ _, rfl⟩
    intro h
    have h1 : p 0 < p (Fin.succ i) := hmono (Fin.succ_pos i)
    rw [h, hzero] at h1
    exact lt_irrefl _ h1
  · rintro ⟨hv, i, -, rfl⟩
    have hi : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exfalso
        apply hv
        rw [← hzero]
        congr 1
        exact Fin.ext h
      · exact h
    refine ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    exact Fin.ext (by simp only [Fin.val_succ]; omega)

theorem prod_activity {m : ℕ} {p : Path k m} (hp : admissible k m p) :
    ∏ i : Fin m, activity (p (Fin.castSucc i))
      = ∏ v ∈ (vertexSet p).erase ⟨k, Nat.lt_succ_self k⟩, activity v := by
  rw [← image_castSucc hp, Finset.prod_image]
  intro i _ j _ h
  exact Fin.castSucc_inj.mp ((admissible_strictMono hp).injective h)

/-- `j - 1 ∈ V` iff the jump into `j` has size one. -/
theorem hasPred_iff {m : ℕ} {p : Path k m} (hp : admissible k m p) (i : Fin m) :
    hasPred (vertexSet p) (p (Fin.succ i)) ↔ (p (Fin.succ i)).val = (p (Fin.castSucc i)).val + 1 := by
  have hmono := admissible_strictMono hp
  have hlt : (p (Fin.castSucc i)).val < (p (Fin.succ i)).val := hmono Fin.castSucc_lt_succ
  constructor
  · rintro ⟨u, hu, hu1⟩
    unfold vertexSet at hu
    rw [Finset.mem_image] at hu
    obtain ⟨i', -, rfl⟩ := hu
    have h1 : i' < Fin.succ i := hmono.lt_iff_lt.mp (Fin.lt_def.mpr (by omega))
    have h2 : i' ≤ Fin.castSucc i := Fin.le_castSucc_iff.mpr h1
    have h3 : (p i').val ≤ (p (Fin.castSucc i)).val := Fin.le_def.mp (hmono.monotone h2)
    omega
  · intro h
    refine ⟨p (Fin.castSucc i), ?_, h.symm⟩
    unfold vertexSet
    rw [Finset.mem_image]
    exact ⟨Fin.castSucc i, Finset.mem_univ _, rfl⟩

theorem prod_stepKernel {m : ℕ} {p : Path k m} (hp : admissible k m p) (θ : ℝ) :
    ∏ i : Fin m, stepKernel k θ (p (Fin.succ i)) (p (Fin.castSucc i))
      = ∏ j ∈ (vertexSet p).erase ⟨0, Nat.zero_lt_succ k⟩,
          (if hasPred (vertexSet p) j then 1 else θ) := by
  have hmono := admissible_strictMono hp
  rw [← image_succ hp, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _
    have hlt : p (Fin.castSucc i) < p (Fin.succ i) := hmono Fin.castSucc_lt_succ
    unfold stepKernel
    rw [ite_eq_left hlt]
    by_cases h : (p (Fin.succ i)).val = (p (Fin.castSucc i)).val + 1
    · rw [ite_eq_left h, ite_eq_left ((hasPred_iff hp i).mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hasPred_iff hp i).mp h'))]
  · intro i _ j _ h
    exact Fin.succ_inj.mp (hmono.injective h)

/-- The path weight under the step kernel, through the vertex set. -/
theorem pathWeight_eq_subWeight {m : ℕ} {p : Path k m} (hp : admissible k m p) (θ : ℝ) :
    pathWeight k m (stepKernel k θ) p = subWeight k θ (vertexSet p) := by
  unfold pathWeight subWeight stepWeight
  rw [Finset.prod_mul_distrib, ← map_prod MvPolynomial.C, prod_stepKernel hp θ,
    prod_activity hp]

/-! ## Prefix visits through the vertex set -/

theorem prefixVisits_eq_prefixCount {m : ℕ} {p : Path k m} (hp : admissible k m p)
    (q : ℕ) (hqk : q < k) : prefixVisits k m q p = prefixCount q (vertexSet p) := by
  have hmono := admissible_strictMono hp
  have hzero : p (0 : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ k⟩ := hp.1
  have hlast : p (Fin.last m) = ⟨k, Nat.lt_succ_self k⟩ := hp.2.1
  unfold prefixVisits prefixCount
  apply Finset.card_bij (fun i _ => p i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hi0, him, hiq⟩ := hi
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, hiq⟩
    · unfold vertexSet
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · have h1 : p 0 < p i := hmono (Fin.lt_def.mpr hi0)
      rw [hzero] at h1
      exact h1
  · intro i _ j _ h
    exact hmono.injective h
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hv, hv0, hvq⟩ := hv
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
        rw [e, hlast] at hvq
        exact absurd hvq (not_le_of_gt hqk)

/-! ## The bijection between paths and vertex sets -/

/-- The path with a given vertex set of cardinality `m + 1`. -/
noncomputable def pathOf {m : ℕ} (V : Finset (Vertex k)) (h : V.card = m + 1) : Path k m :=
  fun i => V.orderEmbOfFin h i

theorem pathOf_mem {m : ℕ} (V : Finset (Vertex k)) (h : V.card = m + 1) (i : Fin (m + 1)) :
    pathOf V h i ∈ V :=
  Finset.orderEmbOfFin_mem V h i

theorem pathOf_strictMono {m : ℕ} (V : Finset (Vertex k)) (h : V.card = m + 1) :
    StrictMono (pathOf V h) :=
  (V.orderEmbOfFin h).strictMono

theorem exists_pathOf_eq {m : ℕ} (V : Finset (Vertex k)) (h : V.card = m + 1)
    {v : Vertex k} (hv : v ∈ V) : ∃ i, pathOf V h i = v := by
  have hr := Finset.range_orderEmbOfFin V h
  have : v ∈ Set.range (V.orderEmbOfFin h) := by
    rw [hr]
    exact hv
  obtain ⟨i, hi⟩ := this
  exact ⟨i, hi⟩

theorem vertexSet_pathOf {m : ℕ} (V : Finset (Vertex k)) (h : V.card = m + 1) :
    vertexSet (pathOf V h) = V := by
  ext v
  unfold vertexSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact pathOf_mem V h i
  · intro hv
    obtain ⟨i, hi⟩ := exists_pathOf_eq V h hv
    exact ⟨i, Finset.mem_univ _, hi⟩

theorem pathOf_admissible {m : ℕ} {V : Finset (Vertex k)} (hV : V ∈ vertexSets k m) :
    admissible k m (pathOf V (mem_vertexSets.mp hV).2.2) := by
  obtain ⟨h0, hk, hc⟩ := mem_vertexSets.mp hV
  have hmono := pathOf_strictMono V hc
  refine ⟨?_, ?_, fun i => hmono Fin.castSucc_lt_succ⟩
  · obtain ⟨i0, hi0⟩ := exists_pathOf_eq V hc h0
    have h1 : pathOf V hc 0 ≤ pathOf V hc i0 := hmono.monotone (Fin.zero_le i0)
    rw [hi0] at h1
    exact Fin.ext (Nat.le_antisymm (Fin.le_def.mp h1) (Nat.zero_le _))
  · obtain ⟨ik, hik⟩ := exists_pathOf_eq V hc hk
    have h1 : pathOf V hc ik ≤ pathOf V hc (Fin.last m) := hmono.monotone (Fin.le_last ik)
    rw [hik] at h1
    have h2 := Fin.le_def.mp h1
    have h3 := Nat.le_of_lt_succ (pathOf V hc (Fin.last m)).isLt
    exact Fin.ext (by simp only [Fin.last] at h2 h3 ⊢; omega)

theorem pathOf_vertexSet {m : ℕ} {p : Path k m} (hp : admissible k m p)
    (h : (vertexSet p).card = m + 1) : pathOf (vertexSet p) h = p := by
  unfold pathOf
  symm
  apply Finset.orderEmbOfFin_unique h
  · intro i
    unfold vertexSet
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · exact admissible_strictMono hp

/-- A sum over admissible paths is a sum over their vertex sets. -/
theorem sum_paths_eq_sum_vertexSets (m : ℕ) (F : Path k m → Poly k)
    (G : Finset (Vertex k) → Poly k) (hFG : ∀ p, admissible k m p → F p = G (vertexSet p)) :
    ∑ p ∈ paths k m, F p = ∑ V ∈ vertexSets k m, G V := by
  refine Finset.sum_bij' (fun p _ => vertexSet p)
    (fun V hV => pathOf V (mem_vertexSets.mp hV).2.2) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact vertexSet_mem (mem_paths.mp hp)
  · intro V hV
    exact mem_paths.mpr (pathOf_admissible hV)
  · intro p hp
    exact pathOf_vertexSet (mem_paths.mp hp) _
  · intro V hV
    exact vertexSet_pathOf V _
  · intro p hp
    exact hFG p (mem_paths.mp hp)

/-- The prefix count array of the step kernel as a sum over vertex sets. -/
theorem prefixArray_stepKernel (θ : ℝ) (q : ℕ) (hqk : q < k) (r s : ℕ) :
    prefixArray k q r s (stepKernel k θ)
      = ∑ V ∈ vertexSets k (r + 1),
          if prefixCount q V = s then subWeight k θ V else 0 := by
  unfold prefixArray
  apply sum_paths_eq_sum_vertexSets
  intro p hp
  rw [prefixVisits_eq_prefixCount hp q hqk, pathWeight_eq_subWeight hp θ]

end CommonTime