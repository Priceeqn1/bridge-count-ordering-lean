import Mathlib

/-!
# Exact formal vocabulary for the Version 1.5 count-array theorem

Indices: `Fin (k+1)` represents the states 0,...,k.
Polynomials: `MvPolynomial (Fin (k+1)) ℝ`; the variables X₁,...,X_{k-1}
are the independent positive site activities; a₀ = 1. X₀ and X_k
exist formally but cannot appear in an admissible path monomial.

A length-m path is a *strictly increasing* function on vertex times
0,...,m, starting at 0 and ending at k. `paths` is the FINITE set of
these paths, hence there is no probabilistic normalization issue.

This file specifies the theorem *exactly* (no finite endpoint cap).
It has not been Lean-typechecked in the current runtime.
-/

namespace CommonTime

abbrev Poly (k : ℕ) := MvPolynomial (Fin (k + 1)) ℝ
abbrev Vertex (k : ℕ) := Fin (k + 1)
abbrev Path (k m : ℕ) := Fin (m + 1) → Vertex k

def CoeffNonneg {k : ℕ} (p : Poly k) : Prop :=
  ∀ exponents : (Fin (k + 1) →₀ ℕ),
    0 ≤ p.coeff exponents

def CoeffLe {k : ℕ} (p q : Poly k) : Prop :=
  CoeffNonneg (q - p)

def StrictLowerTriangular {k : ℕ} (K : Vertex k → Vertex k → ℝ) : Prop :=
  ∀ n j, n ≤ j → K n j = 0

def PositiveAdmissible {k : ℕ} (K : Vertex k → Vertex k → ℝ) : Prop :=
  ∀ n j, j < n → 0 < K n j

def FullTP2 {k : ℕ} (K : Vertex k → Vertex k → ℝ) : Prop :=
  ∀ u v i j, u < v → i < j →
    0 ≤ K u i * K v j - K u j * K v i

def PositiveColumnTP2 {k : ℕ} (K : Vertex k → Vertex k → ℝ) : Prop :=
  ∀ u v i j, u < v → i < j → 0 < i.val →
    0 ≤ K u i * K v j - K u j * K v i

noncomputable def activity {k : ℕ} (j : Vertex k) : Poly k :=
  if j.val = 0 then 1 else MvPolynomial.X j

noncomputable def stepWeight {k : ℕ}
    (K : Vertex k → Vertex k → ℝ) (n j : Vertex k) : Poly k :=
  MvPolynomial.C (K n j) * activity j

def admissible (k m : ℕ) (p : Path k m) : Prop :=
  p ⟨0, Nat.zero_lt_succ m⟩ = ⟨0, Nat.zero_lt_succ k⟩ ∧
  p ⟨m, Nat.lt_succ_self m⟩ = ⟨k, Nat.lt_succ_self k⟩ ∧
  ∀ i : Fin m, p i.castSucc < p i.succ

noncomputable def paths (k m : ℕ) : Finset (Path k m) := by
  classical
  exact Finset.univ.filter (admissible k m)

noncomputable def pathWeight (k m : ℕ)
    (K : Vertex k → Vertex k → ℝ) (p : Path k m) : Poly k :=
  ∏ i : Fin m, stepWeight K (p i.succ) (p i.castSucc)

/-- Increasing partial path starting at 0 and ending at any state z. -/
def admissibleTo (k m : ℕ) (z : Vertex k) (p : Path k m) : Prop :=
  p ⟨0, Nat.zero_lt_succ m⟩ = ⟨0, Nat.zero_lt_succ k⟩ ∧
  p ⟨m, Nat.lt_succ_self m⟩ = z ∧
  ∀ i : Fin m, p i.castSucc < p i.succ

noncomputable def pathsTo (k m : ℕ) (z : Vertex k) : Finset (Path k m) := by
  classical
  exact Finset.univ.filter (admissibleTo k m z)

/-- The transition matrix T(n,j) = K(n,j)*a_j, with a_0=1. -/
noncomputable def transitionMatrix (k : ℕ)
    (K : Vertex k → Vertex k → ℝ) : Matrix (Vertex k) (Vertex k) (Poly k) :=
  fun n j => stepWeight K n j

/-- h_t(z) = (T^t)(k,z) is the backward time/state polynomial. -/
noncomputable def backwardWeight (k t : ℕ)
    (K : Vertex k → Vertex k → ℝ) (z : Vertex k) : Poly k :=
  ((transitionMatrix k K) ^ t) ⟨k, Nat.lt_succ_self k⟩ z

/-- A strict path first crosses above q at jump rho+1. -/
def crossesAt (k theta q rho : ℕ) (p : Path k theta) : Prop :=
  ∃ (h : rho < theta),
    (p ⟨rho, Nat.lt_succ_of_lt h⟩).val ≤ q ∧
    q < (p ⟨rho + 1, Nat.succ_lt_succ h⟩).val

/-- E^theta_rho(z): paths 0 → z of theta jumps, crossing q at rho+1. -/
noncomputable def crossingWeight (k theta q rho : ℕ)
    (K : Vertex k → Vertex k → ℝ) (z : Vertex k) : Poly k := by
  classical
  exact ∑ p ∈ pathsTo k theta z,
    if crossesAt k theta q rho p then pathWeight k theta K p else 0

noncomputable def prefixVisits (k m q : ℕ) (p : Path k m) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun (i : Fin (m + 1)) => 0 < i.val ∧ i.val < m ∧ (p i).val ≤ q)).card

noncomputable def suffixVisits (k m q : ℕ) (p : Path k m) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun (i : Fin (m + 1)) => 0 < i.val ∧ i.val < m ∧ q ≤ (p i).val)).card

noncomputable def prefixArray (k q r s : ℕ)
    (K : Vertex k → Vertex k → ℝ) : Poly k := by
  classical
  exact ∑ p ∈ paths k (r + 1),
    if prefixVisits k (r + 1) q p = s
      then pathWeight k (r + 1) K p else 0

noncomputable def suffixArray (k q r s : ℕ)
    (K : Vertex k → Vertex k → ℝ) : Poly k := by
  classical
  exact ∑ p ∈ paths k (r + 1),
    if suffixVisits k (r + 1) q p = s
      then pathWeight k (r + 1) K p else 0

noncomputable def jumpCountWeight (k m : ℕ)
    (K : Vertex k → Vertex k → ℝ) : Poly k := by
  classical
  exact ∑ p ∈ paths k m, pathWeight k m K p

noncomputable def minor {k : ℕ} (a b c d : Poly k) : Poly k :=
  a * d - b * c

end CommonTime
