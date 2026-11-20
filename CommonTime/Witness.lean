import CommonTime.Coefficient

open scoped symmDiff

namespace CommonTime

variable {k : ℕ}

theorem coeff_ite_zero (c : Prop) [Decidable c] (P : Poly k) (e : Fin (k + 1) →₀ ℕ) :
    (if c then P else 0).coeff e = if c then P.coeff e else 0 := by
  split_ifs <;> simp

open Classical in
theorem coeff_pair' (θ : ℝ) (hθ : θ ≠ 0) (A B : Finset (Vertex k))
    (h1 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ A)
    (h2 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ B) (e : Fin (k + 1) →₀ ℕ) :
    (subWeight k θ A * subWeight k θ B).coeff e
      = (θ ^ (A.card - 1) * (θ⁻¹) ^ adjCount (vertexNat A))
        * (θ ^ (B.card - 1) * (θ⁻¹) ^ adjCount (vertexNat B))
        * (if expo A + expo B = e then 1 else 0) := by
  rw [subWeight_eq θ hθ A h1, subWeight_eq θ hθ B h2, actProd_eq A, actProd_eq B,
    MvPolynomial.C_mul_monomial, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.coeff_monomial]
  split_ifs <;> simp

/-- Exponent pattern `a₁ a₃ a₄` on `Fin 6`. -/
noncomputable def eW : Fin 6 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![0, 1, 0, 1, 1, 0]

theorem expo_add_eq_eW (A B : Finset (Fin 6)) :
    expo A + expo B = eW ↔
      ∀ j : Fin 6, ((if (j ∈ A ∧ j ≠ 5 ∧ j.val ≠ 0) then 1 else 0)
        + (if (j ∈ B ∧ j ≠ 5 ∧ j.val ≠ 0) then 1 else 0)) = (![0, 1, 0, 1, 1, 0] : Fin 6 → ℕ) j := by
  rw [Finsupp.ext_iff]
  simp only [Finsupp.add_apply, expo_apply]
  rfl

example : vertexSets 5 2 = {{0,1,5},{0,2,5},{0,3,5},{0,4,5}} := by decide
example : vertexSets 5 3 = {{0,1,2,5},{0,1,3,5},{0,1,4,5},{0,2,3,5},{0,2,4,5},{0,3,4,5}} := by decide


theorem witness_coeff {θ : ℝ} (hθ : θ ≠ 0) :
    (minor (prefixArray 5 1 1 0 (stepKernel 5 θ)) (prefixArray 5 1 1 1 (stepKernel 5 θ))
      (prefixArray 5 1 2 0 (stepKernel 5 θ)) (prefixArray 5 1 2 1 (stepKernel 5 θ))).coeff eW
      = θ ^ 2 * (2 * θ - 1) := by
  classical
  rw [minor_expand θ 1 (by norm_num) 1 2 0 1]
  simp only [MvPolynomial.coeff_sum]
  have key : ∀ A ∈ vertexSets 5 3, ∀ B ∈ vertexSets 5 2,
      ((if prefixCount 1 A = 1 ∧ prefixCount 1 B = 0
              then subWeight 5 θ A * subWeight 5 θ B else 0)
            - (if prefixCount 1 A = 0 ∧ prefixCount 1 B = 1
              then subWeight 5 θ A * subWeight 5 θ B else 0)).coeff eW
        = ((if prefixCount 1 A = 1 ∧ prefixCount 1 B = 0 then (1:ℝ) else 0)
            - (if prefixCount 1 A = 0 ∧ prefixCount 1 B = 1 then 1 else 0))
          * ((θ ^ (A.card - 1) * (θ⁻¹) ^ adjCount (vertexNat A))
            * (θ ^ (B.card - 1) * (θ⁻¹) ^ adjCount (vertexNat B))
            * (if expo A + expo B = eW then 1 else 0)) := by
    intro A hA B hB
    rw [mem_vertexSets] at hA hB
    rw [MvPolynomial.coeff_sub, coeff_ite_zero, coeff_ite_zero,
      coeff_pair' θ hθ A B hA.1 hB.1]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun A hA => Finset.sum_congr rfl (key A hA))]
  have h2 : vertexSets 5 2 = {{0,1,5},{0,2,5},{0,3,5},{0,4,5}} := by decide
  have h3 : vertexSets 5 3 = {{0,1,2,5},{0,1,3,5},{0,1,4,5},{0,2,3,5},{0,2,4,5},{0,3,4,5}} := by decide
  rw [h2, h3]
  simp only [expo_add_eq_eW]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton]
  have a1 : ({0,1,4,5} : Finset (Fin 6)).card = 4 := by decide
  have a2 : ({0,1,3,5} : Finset (Fin 6)).card = 4 := by decide
  have a3 : ({0,3,4,5} : Finset (Fin 6)).card = 4 := by decide
  have b1 : ({0,3,5} : Finset (Fin 6)).card = 3 := by decide
  have b2 : ({0,4,5} : Finset (Fin 6)).card = 3 := by decide
  have b3 : ({0,1,5} : Finset (Fin 6)).card = 3 := by decide
  have c1 : adjCount (vertexNat ({0,1,4,5} : Finset (Fin 6))) = 2 := by decide
  have c2 : adjCount (vertexNat ({0,1,3,5} : Finset (Fin 6))) = 1 := by decide
  have c3 : adjCount (vertexNat ({0,3,4,5} : Finset (Fin 6))) = 2 := by decide
  have d1 : adjCount (vertexNat ({0,3,5} : Finset (Fin 6))) = 0 := by decide
  have d2 : adjCount (vertexNat ({0,4,5} : Finset (Fin 6))) = 1 := by decide
  have d3 : adjCount (vertexNat ({0,1,5} : Finset (Fin 6))) = 1 := by decide
  simp only [a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, ite_false, ite_true, sub_zero, zero_sub,
    zero_mul, mul_zero, mul_one, one_mul, zero_add, add_zero, neg_zero, neg_mul]
  have hu : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ
  simp only [Nat.reduceSub]
  linear_combination (2 * θ ^ 3 * (θ * θ⁻¹ + 1) - θ ^ 2 * ((θ * θ⁻¹) ^ 2 + θ * θ⁻¹ + 1)) * hu

end CommonTime
