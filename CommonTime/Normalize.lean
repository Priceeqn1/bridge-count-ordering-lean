import CommonTime.Subsets
import CommonTime.Bonds

/-!
# Normalization of the path weight (Theorem 4.7, step 4a)

For the Toeplitz kernel of display (28), the kernel factor of the path with
vertex set `V` is `θ` raised to the number of vertices of `V \ {0}` whose
predecessor is not in `V`. With `ψ = θ⁻¹` this is

  `θ^(|V| - 1) · ψ^(adj V)`,   `adj V = #{u ∈ V : u + 1 ∈ V}`,

which is the form used by `pair_bond_factor` (`Bonds.lean`).
-/

namespace CommonTime

variable {k : ℕ}

/-- The vertex set as a set of natural numbers. -/
def vertexNat (V : Finset (Vertex k)) : Finset ℕ := V.image Fin.val

/-- The number of vertices of `V \ {0}` with a predecessor in `V` is `adj V`. -/
theorem card_hasPred_eq_adjCount (V : Finset (Vertex k)) :
    ((V.erase ⟨0, Nat.zero_lt_succ k⟩).filter (fun j => hasPred V j)).card
      = adjCount (vertexNat V) := by
  unfold adjCount
  apply Finset.card_bij (fun j _ => j.val - 1)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_erase] at hj
    obtain ⟨⟨_, hjV⟩, u, huV, hu⟩ := hj
    rw [Finset.mem_filter]
    unfold vertexNat
    have hj1 : j.val - 1 = u.val := by omega
    refine ⟨Finset.mem_image.mpr ⟨u, huV, hj1.symm⟩, ?_⟩
    have : j.val - 1 + 1 = j.val := by omega
    rw [this]
    exact Finset.mem_image.mpr ⟨j, hjV, rfl⟩
  · intro j₁ h₁ j₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    obtain ⟨u₁, _, hu₁⟩ := h₁.2
    obtain ⟨u₂, _, hu₂⟩ := h₂.2
    apply Fin.ext
    omega
  · intro b hb
    rw [Finset.mem_filter] at hb
    unfold vertexNat at hb
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨u, huV, hu⟩ := Finset.mem_image.mp hb1
    obtain ⟨w, hwV, hw⟩ := Finset.mem_image.mp hb2
    have hmem : w ∈ (V.erase ⟨0, Nat.zero_lt_succ k⟩).filter (fun j => hasPred V j) := by
      rw [Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨?_, hwV⟩, u, huV, by omega⟩
      intro h
      have h' : w.val = 0 := congrArg Fin.val h
      omega
    exact ⟨w, hmem, by omega⟩

/-- **Normalization.** For `θ ≠ 0` and `0 ∈ V`, the kernel factor of the path
    with vertex set `V` is `θ^(|V|-1) · (θ⁻¹)^(adj V)`. -/
theorem kernelFactor_eq (θ : ℝ) (hθ : θ ≠ 0) (V : Finset (Vertex k))
    (h0 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ V) :
    ∏ j ∈ V.erase ⟨0, Nat.zero_lt_succ k⟩, (if hasPred V j then (1 : ℝ) else θ)
      = θ ^ (V.card - 1) * (θ⁻¹) ^ adjCount (vertexNat V) := by
  have hc : (V.erase ⟨0, Nat.zero_lt_succ k⟩).card = V.card - 1 :=
    Finset.card_erase_of_mem h0
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := V.erase ⟨0, Nat.zero_lt_succ k⟩) (fun j => hasPred V j)
  rw [card_hasPred_eq_adjCount, hc] at hsplit
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [← hsplit, pow_add, mul_comm (θ ^ _), mul_assoc, ← mul_pow, mul_inv_cancel₀ hθ,
    one_pow, mul_one]

open scoped symmDiff

/-- The path weight with the kernel factor made explicit. -/
theorem subWeight_eq (θ : ℝ) (hθ : θ ≠ 0) (V : Finset (Vertex k))
    (h0 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ V) :
    subWeight k θ V
      = MvPolynomial.C (θ ^ (V.card - 1) * (θ⁻¹) ^ adjCount (vertexNat V))
          * ∏ v ∈ V.erase ⟨k, Nat.lt_succ_self k⟩, activity v := by
  unfold subWeight
  rw [kernelFactor_eq θ hθ V h0]

/-- **Pair weight.** The product of the weights of two paths is a real
    coefficient times the product of their activity monomials, and the real
    coefficient is `θ^(|V₁|+|V₂|-2) · ψ^{C₀} · bondWeight ψ D E` with `ψ = θ⁻¹`,
    `D = V₁ ∆ V₂`, `E = V₁ \ V₂`. -/
theorem subWeight_pair (θ : ℝ) (hθ : θ ≠ 0) (V₁ V₂ : Finset (Vertex k))
    (h1 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ V₁)
    (h2 : (⟨0, Nat.zero_lt_succ k⟩ : Vertex k) ∈ V₂) :
    subWeight k θ V₁ * subWeight k θ V₂
      = MvPolynomial.C
          (θ ^ (V₁.card - 1) * θ ^ (V₂.card - 1)
            * ((θ⁻¹) ^ baseCount (vertexNat V₁) (vertexNat V₂)
              * bondWeight θ⁻¹ (vertexNat V₁ ∆ vertexNat V₂) (vertexNat V₁ \ vertexNat V₂)))
        * ((∏ v ∈ V₁.erase ⟨k, Nat.lt_succ_self k⟩, activity v)
            * ∏ v ∈ V₂.erase ⟨k, Nat.lt_succ_self k⟩, activity v) := by
  rw [subWeight_eq θ hθ V₁ h1, subWeight_eq θ hθ V₂ h2]
  have hp := pair_bond_factor θ⁻¹ (vertexNat V₁) (vertexNat V₂)
  have e : θ ^ (V₁.card - 1) * θ⁻¹ ^ adjCount (vertexNat V₁)
        * (θ ^ (V₂.card - 1) * θ⁻¹ ^ adjCount (vertexNat V₂))
      = θ ^ (V₁.card - 1) * θ ^ (V₂.card - 1)
          * ((θ⁻¹) ^ baseCount (vertexNat V₁) (vertexNat V₂)
            * bondWeight θ⁻¹ (vertexNat V₁ ∆ vertexNat V₂) (vertexNat V₁ \ vertexNat V₂)) := by
    rw [← hp]
    ring
  rw [← e]
  simp only [map_mul]
  ring

end CommonTime
