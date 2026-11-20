import Mathlib

/-!
# Coupled binary chains (manuscript Lemma 4.8, revised Section 4.3)

A binary chain on sites `1, …, N` with equal-neighbour couplings
`φ₁, …, φ_{N-1}` assigns to `η ∈ {0,1}^N` the weight
`∏ φᵤ^{1{ηᵤ = ηᵤ₊₁}}`. Classifying by the number of ones `i` and the last bit
`ε` gives two sequences `A₀(i), A₁(i)`. Adding a site with coupling `φ`
updates them by

  `A₀'(i) = φ A₀(i) + A₁(i)`,   `A₁'(i) = A₀(i-1) + φ A₁(i-1)`.

This file takes that recursion as the definition (`chain`), with the
couplings listed most-recent-first, and proves, for couplings in `[1, 2]`:

* (i)   `A₁(i) = A₀(N - i)`                       (`a1_reflect`);
* (ii)  `c = A₀ + A₁` is symmetric unimodal        (`c_symm`, `w_nonneg`);
* (iii) `0 ≤ d(i) = A₁(i) - A₀(i)` for `2 i ≥ N`   (`d_nonneg`);
* (iv)  `A₁(i-1) ≤ A₁(i)` for `2 i ≤ N + 1`         (`a1_mono`),
        equivalently `A₀` is nonincreasing on `2 u ≥ N - 1`.

Then, for two chains joined through a cut bond with coupling `κ ≥ 1`, the
cut-difference inequality `Z(i₊, j₊) ≥ Z(i₋, j₋)` of the proof of
Theorem 4.7 (`Zdiff_nonneg`).

Indices are integers; values outside `0 … N` are zero by construction.
Nothing here depends on the path model; the connection to count arrays is
made in a separate file.
-/

namespace CommonTime

/-- The two sequences `A₀, A₁` of a chain, indexed by integers. -/
structure ChainState where
  a0 : ℤ → ℝ
  a1 : ℤ → ℝ

/-- Adding one site with coupling `φ`. -/
def chainStep (φ : ℝ) (A : ChainState) : ChainState :=
  ⟨fun i => φ * A.a0 i + A.a1 i, fun i => A.a0 (i - 1) + φ * A.a1 (i - 1)⟩

/-- The one-site chain. -/
def chainOne : ChainState :=
  ⟨fun i => if i = 0 then 1 else 0, fun i => if i = 1 then 1 else 0⟩

/-- The chain with couplings `l`, listed most-recent-first. -/
def chain : List ℝ → ChainState
  | [] => chainOne
  | φ :: l => chainStep φ (chain l)

/-- Number of sites. -/
def sites (l : List ℝ) : ℤ := (l.length : ℤ) + 1

/-- All couplings lie in `[1, 2]`. -/
def Couplings (l : List ℝ) : Prop := ∀ φ ∈ l, 1 ≤ φ ∧ φ ≤ 2

/-- `c = A₀ + A₁`. -/
def cseq (l : List ℝ) (i : ℤ) : ℝ := (chain l).a0 i + (chain l).a1 i

/-- `d = A₁ - A₀`. -/
def dseq (l : List ℝ) (i : ℤ) : ℝ := (chain l).a1 i - (chain l).a0 i

/-- Forward difference `w(i) = c(i) - c(i-1)`. -/
def wseq (l : List ℝ) (i : ℤ) : ℝ := cseq l i - cseq l (i - 1)

theorem sites_cons (φ : ℝ) (l : List ℝ) : sites (φ :: l) = sites l + 1 := by
  simp [sites]

theorem sites_nil : sites [] = 1 := by
  norm_num [sites]

theorem couplings_tail {φ : ℝ} {l : List ℝ} (h : Couplings (φ :: l)) : Couplings l :=
  fun ψ hψ => h ψ (List.mem_cons_of_mem φ hψ)

theorem couplings_head {φ : ℝ} {l : List ℝ} (h : Couplings (φ :: l)) : 1 ≤ φ ∧ φ ≤ 2 :=
  h φ (List.mem_cons_self)

/-! ## Unfolding lemmas -/

theorem a0_cons (φ : ℝ) (l : List ℝ) (i : ℤ) :
    (chain (φ :: l)).a0 i = φ * (chain l).a0 i + (chain l).a1 i := rfl

theorem a1_cons (φ : ℝ) (l : List ℝ) (i : ℤ) :
    (chain (φ :: l)).a1 i = (chain l).a0 (i - 1) + φ * (chain l).a1 (i - 1) := rfl

theorem a0_nil (i : ℤ) : (chain []).a0 i = if i = 0 then 1 else 0 := rfl

theorem a1_nil (i : ℤ) : (chain []).a1 i = if i = 1 then 1 else 0 := rfl

/-! ## Nonnegativity -/

theorem a_nonneg {l : List ℝ} (h : Couplings l) (i : ℤ) :
    0 ≤ (chain l).a0 i ∧ 0 ≤ (chain l).a1 i := by
  induction l generalizing i with
  | nil =>
    rw [a0_nil, a1_nil]
    constructor <;> split_ifs <;> norm_num
  | cons φ l ih =>
    have hφ := (couplings_head h).1
    have ih' := ih (couplings_tail h)
    rw [a0_cons, a1_cons]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) (ih' i).1) (ih' i).2
    · exact add_nonneg (ih' (i - 1)).1 (mul_nonneg (by linarith) (ih' (i - 1)).2)

theorem c_nonneg {l : List ℝ} (h : Couplings l) (i : ℤ) : 0 ≤ cseq l i :=
  add_nonneg (a_nonneg h i).1 (a_nonneg h i).2

/-! ## (i) Reflection symmetry -/

theorem a1_reflect (l : List ℝ) (i : ℤ) : (chain l).a1 i = (chain l).a0 (sites l - i) := by
  induction l generalizing i with
  | nil =>
    rw [a0_nil, a1_nil, sites_nil]
    by_cases h : i = 1
    · rw [ite_eq_left h, ite_eq_left (show 1 - i = 0 by omega)]
    · rw [ite_eq_right h, ite_eq_right (show ¬ 1 - i = 0 by omega)]
  | cons φ l ih =>
    rw [a1_cons, a0_cons, sites_cons]
    have e1 : (chain l).a1 (i - 1) = (chain l).a0 (sites l + 1 - i) := by
      rw [ih (i - 1)]
      congr 1
      ring
    have e2 : (chain l).a1 (sites l + 1 - i) = (chain l).a0 (i - 1) := by
      rw [ih (sites l + 1 - i)]
      congr 1
      ring
    rw [e1, e2]
    ring

theorem a0_reflect (l : List ℝ) (i : ℤ) : (chain l).a0 i = (chain l).a1 (sites l - i) := by
  rw [a1_reflect]
  congr 1
  ring

theorem c_symm (l : List ℝ) (i : ℤ) : cseq l i = cseq l (sites l - i) := by
  unfold cseq
  rw [a1_reflect l i, a0_reflect l i]
  ring

theorem d_antisymm (l : List ℝ) (i : ℤ) : dseq l i = -dseq l (sites l - i) := by
  unfold dseq
  rw [a1_reflect l i, a0_reflect l i]
  ring

/-! ## (ii) Symmetric unimodality -/

/-- The two-term recursion for `c`. -/
theorem c_cons (φ : ℝ) (l : List ℝ) (i : ℤ) :
    cseq (φ :: l) i
      = φ * (cseq l i + cseq l (i - 1)) - (φ - 1) * ((chain l).a1 i + (chain l).a0 (i - 1)) := by
  unfold cseq
  rw [a0_cons, a1_cons]
  ring

/-- The quantity killed by the three-term recurrence, one step back. -/
theorem a1_add_a0_cons (φ' : ℝ) (l' : List ℝ) (i : ℤ) :
    (chain (φ' :: l')).a1 i + (chain (φ' :: l')).a0 (i - 1) = (φ' + 1) * cseq l' (i - 1) := by
  unfold cseq
  rw [a1_cons, a0_cons]
  ring

theorem w_nil (i : ℤ) : wseq [] i = (if i = 0 then 1 else 0) - (if i = 2 then 1 else 0) := by
  unfold wseq cseq
  simp only [a0_nil, a1_nil]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2) by omega) with h | h | h | h
  · subst h
    norm_num
  · subst h
    norm_num
  · subst h
    norm_num
  · obtain ⟨h0, h1, h2⟩ := h
    split_ifs <;> first | omega | norm_num

theorem w_cons_nil (φ : ℝ) (i : ℤ) :
    wseq [φ] i = (if i = 0 then φ else 0) + (if i = 1 then 2 - φ else 0)
      + (if i = 2 then φ - 2 else 0) + (if i = 3 then -φ else 0) := by
  unfold wseq cseq
  simp only [a0_cons, a1_cons, a0_nil, a1_nil]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3) by omega)
    with h | h | h | h | h
  · subst h
    norm_num
  · subst h
    norm_num
  · subst h
    norm_num
  · subst h
    norm_num
  · obtain ⟨h0, h1, h2, h3⟩ := h
    split_ifs <;> first | omega | norm_num

/-- From nonnegativity of `w` on `2 i ≤ N`, nonnegativity on `2 i ≤ N + 1`
    (the extra case is the midpoint, where `w = 0` by symmetry). -/
theorem w_nonneg_of_half (l : List ℝ) (hw : ∀ i : ℤ, 2 * i ≤ sites l → 0 ≤ wseq l i)
    (i : ℤ) (hi : 2 * i ≤ sites l + 1) : 0 ≤ wseq l i := by
  rcases lt_or_eq_of_le hi with hlt | heq
  · exact hw i (by omega)
  · have e : sites l - i = i - 1 := by omega
    unfold wseq
    rw [c_symm l i, e]
    exact le_of_eq (sub_self _).symm

/-- The joint induction behind unimodality: `w` is nonnegative on the lower
    half, and adding a site with coupling `φ ∈ [1, 2]` multiplies it by at
    least `φ` there. -/
theorem w_induction {l : List ℝ} (h : Couplings l) :
    (∀ i : ℤ, 2 * i ≤ sites l → 0 ≤ wseq l i) ∧
    (∀ φ : ℝ, 1 ≤ φ → φ ≤ 2 → ∀ i : ℤ, 2 * i ≤ sites l + 1 → φ * wseq l i ≤ wseq (φ :: l) i) := by
  induction l with
  | nil =>
    constructor
    · intro i hi
      rw [sites_nil] at hi
      rw [w_nil, ite_eq_right (show ¬ i = 2 by omega)]
      split_ifs <;> norm_num
    · intro φ hφ1 hφ2 i hi
      rw [sites_nil] at hi
      rw [w_nil, w_cons_nil]
      rcases (show i = 0 ∨ i = 1 ∨ (i ≠ 0 ∧ i ≠ 1) by omega) with h | h | h
      · subst h
        norm_num
      · subst h
        norm_num
        linarith
      · obtain ⟨h0, h1⟩ := h
        split_ifs <;> first | omega | norm_num
  | cons φ' l' ih =>
    have hφ' := couplings_head h
    obtain ⟨ih1, ih2⟩ := ih (couplings_tail h)
    have hw' : ∀ i : ℤ, 2 * i ≤ sites l' + 1 → 0 ≤ wseq l' i := w_nonneg_of_half l' ih1
    -- nonnegativity on the lower half for `φ' :: l'`
    have h1 : ∀ i : ℤ, 2 * i ≤ sites (φ' :: l') → 0 ≤ wseq (φ' :: l') i := by
      intro i hi
      rw [sites_cons] at hi
      have := ih2 φ' hφ'.1 hφ'.2 i hi
      have := hw' i hi
      nlinarith
    refine ⟨h1, ?_⟩
    intro φ hφ1 hφ2 i hi
    rw [sites_cons] at hi
    -- the three-term identity for the differences
    have key : wseq (φ :: φ' :: l') i - φ * wseq (φ' :: l') i
        = φ * wseq (φ' :: l') (i - 1) - (φ - 1) * (φ' + 1) * wseq l' (i - 1) := by
      unfold wseq
      rw [c_cons φ (φ' :: l') i, c_cons φ (φ' :: l') (i - 1), a1_add_a0_cons, a1_add_a0_cons]
      have e : i - 1 - 1 = i - 2 := by ring
      rw [e]
      ring
    have hA : φ' * wseq l' (i - 1) ≤ wseq (φ' :: l') (i - 1) :=
      ih2 φ' hφ'.1 hφ'.2 (i - 1) (by omega)
    have hB : 0 ≤ wseq l' (i - 1) := hw' (i - 1) (by omega)
    have hC : 0 ≤ (φ' + 1 - φ) * wseq l' (i - 1) := mul_nonneg (by linarith) hB
    have hD : φ * (φ' * wseq l' (i - 1)) ≤ φ * wseq (φ' :: l') (i - 1) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    nlinarith

/-- (ii): `c` is nondecreasing on the lower half. -/
theorem w_nonneg {l : List ℝ} (h : Couplings l) (i : ℤ) (hi : 2 * i ≤ sites l + 1) :
    0 ≤ wseq l i :=
  w_nonneg_of_half l (w_induction h).1 i hi

theorem c_mono_lower {l : List ℝ} (h : Couplings l) (i : ℤ) (hi : 2 * i ≤ sites l + 1) :
    cseq l (i - 1) ≤ cseq l i := by
  have := w_nonneg h i hi
  unfold wseq at this
  linarith

/-- `c` is nonincreasing on the upper half. -/
theorem c_anti_upper {l : List ℝ} (h : Couplings l) (u : ℤ) (hu : sites l ≤ 2 * u) :
    cseq l (u + 1) ≤ cseq l u := by
  have hm := c_mono_lower h (sites l - u) (by omega)
  rw [c_symm l u, c_symm l (u + 1)]
  have e : sites l - (u + 1) = sites l - u - 1 := by ring
  rw [e]
  exact hm

theorem c_anti_upper' {l : List ℝ} (h : Couplings l) (u : ℤ) (hu : sites l ≤ 2 * u) :
    ∀ n : ℕ, cseq l (u + n) ≤ cseq l u := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have := c_anti_upper h (u + n) (by omega)
    have e : (u + ((n + 1 : ℕ) : ℤ)) = u + n + 1 := by push_cast; ring
    rw [e]
    linarith

/-! ## (iii) Sign of the antisymmetric part -/

theorem d_cons (φ : ℝ) (l : List ℝ) (i : ℤ) :
    dseq (φ :: l) i
      = (φ + 1) / 2 * (cseq l (i - 1) - cseq l i) + (φ - 1) / 2 * (dseq l (i - 1) + dseq l i) := by
  unfold dseq cseq
  rw [a0_cons, a1_cons]
  ring

theorem d_nonneg {l : List ℝ} (h : Couplings l) (i : ℤ) (hi : sites l ≤ 2 * i) :
    0 ≤ dseq l i := by
  induction l generalizing i with
  | nil =>
    rw [sites_nil] at hi
    unfold dseq
    rw [a0_nil, a1_nil, ite_eq_right (show ¬ i = 0 by omega)]
    split_ifs <;> norm_num
  | cons φ l ih =>
    have hφ := couplings_head h
    have hl := couplings_tail h
    rw [sites_cons] at hi
    rw [d_cons]
    by_cases hc : sites l ≤ 2 * (i - 1)
    · have h1 : cseq l i ≤ cseq l (i - 1) := by
        have := c_anti_upper hl (i - 1) hc
        have e : i - 1 + 1 = i := by ring
        rw [e] at this
        exact this
      have h2 := ih hl (i - 1) hc
      have h3 := ih hl i (by omega)
      have h4 : 0 ≤ (φ + 1) / 2 * (cseq l (i - 1) - cseq l i) :=
        mul_nonneg (by linarith) (by linarith)
      have h5 : 0 ≤ (φ - 1) / 2 * (dseq l (i - 1) + dseq l i) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · -- the midpoint case: `sites l = 2 i - 1`
      have e : sites l - i = i - 1 := by omega
      have h1 : cseq l (i - 1) = cseq l i := by
        rw [c_symm l i, e]
      have h2 : dseq l (i - 1) + dseq l i = 0 := by
        rw [d_antisymm l i, e]
        ring
      rw [h1, h2]
      ring_nf
      exact le_refl 0

theorem d_le_c {l : List ℝ} (h : Couplings l) (i : ℤ) : dseq l i ≤ cseq l i := by
  unfold dseq cseq
  have := (a_nonneg h i).1
  linarith

/-! ## (iv) Tail monotonicity -/

theorem a1_mono {l : List ℝ} (h : Couplings l) (i : ℤ) (hi : 2 * i ≤ sites l + 1) :
    (chain l).a1 (i - 1) ≤ (chain l).a1 i := by
  induction l generalizing i with
  | nil =>
    rw [sites_nil] at hi
    rw [a1_nil, a1_nil]
    by_cases h1 : i = 1
    · subst h1
      norm_num
    · rw [ite_eq_right h1, ite_eq_right (show ¬ i - 1 = 1 by omega)]
  | cons φ l ih =>
    have hφ := couplings_head h
    have hl := couplings_tail h
    rw [sites_cons] at hi
    have key : (chain (φ :: l)).a1 i - (chain (φ :: l)).a1 (i - 1)
        = (φ - 1) * ((chain l).a1 (i - 1) - (chain l).a1 (i - 2)) + wseq l (i - 1) := by
      unfold wseq cseq
      rw [a1_cons, a1_cons]
      have e : i - 1 - 1 = i - 2 := by ring
      rw [e]
      ring
    have h1 : (chain l).a1 (i - 2) ≤ (chain l).a1 (i - 1) := by
      have := ih hl (i - 1) (by omega)
      have e : i - 1 - 1 = i - 2 := by ring
      rw [e] at this
      exact this
    have h2 : 0 ≤ wseq l (i - 1) := w_nonneg hl (i - 1) (by omega)
    have h3 : 0 ≤ (φ - 1) * ((chain l).a1 (i - 1) - (chain l).a1 (i - 2)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- `A₀` is nonincreasing from `(N - 1)/2` on. -/
theorem a0_anti_upper {l : List ℝ} (h : Couplings l) (u : ℤ) (hu : sites l - 1 ≤ 2 * u) :
    (chain l).a0 (u + 1) ≤ (chain l).a0 u := by
  rw [a0_reflect l u, a0_reflect l (u + 1)]
  have e : sites l - (u + 1) = sites l - u - 1 := by ring
  rw [e]
  exact a1_mono h (sites l - u) (by omega)

theorem a0_anti_upper' {l : List ℝ} (h : Couplings l) (u : ℤ) (hu : sites l - 1 ≤ 2 * u) :
    ∀ n : ℕ, (chain l).a0 (u + n) ≤ (chain l).a0 u := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have := a0_anti_upper h (u + n) (by omega)
    have e : (u + ((n + 1 : ℕ) : ℤ)) = u + n + 1 := by push_cast; ring
    rw [e]
    linarith

/-! ## The cut-difference inequality -/

/-- Two chains joined through a bond of coupling `κ` between the last site of
    the first and the (reversed) first site of the second:
    `Z(i, j) = Σ_{ε,ε'} κ^{1{ε = ε'}} A_ε(i) B_{ε'}(j)`. -/
def Zpair (κ : ℝ) (A B : ChainState) (i j : ℤ) : ℝ :=
  κ * (A.a0 i * B.a0 j + A.a1 i * B.a1 j) + A.a0 i * B.a1 j + A.a1 i * B.a0 j

/-- The exact difference identity, after reflecting the left index. -/
theorem Zpair_diff (κ : ℝ) (lA lB : List ℝ) (ip jp jm : ℤ) :
    Zpair κ (chain lA) (chain lB) ip jp - Zpair κ (chain lA) (chain lB) (sites lA - ip) jm
      = (κ * (chain lA).a0 ip + (chain lA).a1 ip) * (cseq lB jp - cseq lB jm)
        + (κ - 1) * dseq lA ip * ((chain lB).a1 jp - (chain lB).a0 jm) := by
  unfold Zpair cseq dseq
  rw [a0_reflect lA (sites lA - ip), a1_reflect lA (sites lA - ip)]
  have e : sites lA - (sites lA - ip) = ip := by ring
  rw [e]
  ring

/-- Manuscript inequality `Z(i₊, j₊) ≥ Z(i₋, j₋)` under the index constraints
    `i₋ = N₋ - i₊ < i₊`, `j₊ < j₋`, `j₊ + j₋ ≥ N₊ + 1`, and `κ ≥ 1`. -/
theorem Zdiff_nonneg {lA lB : List ℝ} (hA : Couplings lA) (hB : Couplings lB)
    {κ : ℝ} (hκ : 1 ≤ κ) (ip jp jm : ℤ)
    (hi : sites lA - ip < ip) (hj : jp < jm) (hjs : sites lB + 1 ≤ jp + jm) :
    Zpair κ (chain lA) (chain lB) (sites lA - ip) jm
      ≤ Zpair κ (chain lA) (chain lB) ip jp := by
  have hdiff := Zpair_diff κ lA lB ip jp jm
  -- factor 1
  have f1 : 0 ≤ κ * (chain lA).a0 ip + (chain lA).a1 ip :=
    add_nonneg (mul_nonneg (by linarith) (a_nonneg hA ip).1) (a_nonneg hA ip).2
  -- factor 3: `d₋(i₊) ≥ 0`
  have f3 : 0 ≤ dseq lA ip := d_nonneg hA ip (by omega)
  -- factors 2 and 4, by cases on which side of the midpoint `j₊` lies
  have f24 : cseq lB jm ≤ cseq lB jp ∧ (chain lB).a0 jm ≤ (chain lB).a1 jp := by
    rcases le_or_gt (sites lB) (2 * jp) with hup | hlow
    · -- `j₊` in the upper half: monotonicity from `j₊` to `j₋`, and `d₊(j₊) ≥ 0`
      obtain ⟨n, hn0⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ jm - jp by omega)
      have hn : jm = jp + n := by omega
      constructor
      · have := c_anti_upper' hB jp hup n
        rw [← hn] at this
        exact this
      · have h1 := a0_anti_upper' hB jp (by omega) n
        rw [← hn] at h1
        have h2 := d_nonneg hB jp hup
        unfold dseq at h2
        linarith
    · -- `j₊` in the lower half: reflect to `j₊' = N₊ - j₊ > N₊/2`, then `j₊' < j₋`
      obtain ⟨n, hn0⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ jm - (sites lB - jp) by omega)
      have hn : jm = sites lB - jp + n := by omega
      constructor
      · rw [c_symm lB jp]
        have := c_anti_upper' hB (sites lB - jp) (by omega) n
        rw [← hn] at this
        exact this
      · rw [a1_reflect lB jp]
        have := a0_anti_upper' hB (sites lB - jp) (by omega) n
        rw [← hn] at this
        exact this
  obtain ⟨f2, f4⟩ := f24
  have t1 : 0 ≤ (κ * (chain lA).a0 ip + (chain lA).a1 ip) * (cseq lB jp - cseq lB jm) :=
    mul_nonneg f1 (by linarith)
  have t2 : 0 ≤ (κ - 1) * dseq lA ip * ((chain lB).a1 jp - (chain lB).a0 jm) :=
    mul_nonneg (mul_nonneg (by linarith) f3) (by linarith)
  linarith

end CommonTime
