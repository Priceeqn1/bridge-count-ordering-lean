import Mathlib

/-!
# Two-by-two Cauchy--Binet identity (algebraic core)

This identity is a genuine algebraic proof term (`ring`), not an axiom.
It is an isolated two-state instance; the all-finite-sum Cauchy--Binet
and coefficientwise sign transport still need formalization.
-/

namespace CommonTime

variable {R : Type*} [CommRing R]

theorem cauchy_binet_two_terms
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : R) :
    (a₁ * c₁ + a₂ * c₂) * (b₁ * d₁ + b₂ * d₂)
      - (a₁ * d₁ + a₂ * d₂) * (b₁ * c₁ + b₂ * c₂)
    = (a₁ * b₂ - a₂ * b₁) * (c₁ * d₂ - c₂ * d₁) := by
  ring

end CommonTime
