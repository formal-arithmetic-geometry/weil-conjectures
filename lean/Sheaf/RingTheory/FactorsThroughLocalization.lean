module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FinitePresentation

/-! Auxiliary factorization through a principal localization target. -/

@[expose] public section

universe u₁ v₁ w

namespace Algebra

/-- A map from a finitely presented algebra into a localization factors through a
principal localization. Source: Stacks Project, Algebra, Tags 00CR and 00QO.
(blueprint: lem-factors-through-localization-of-smooth)

Proof: Present C as a polynomial algebra on finitely many generators modulo finitely many
relations. Represent the images of the generators by fractions in P localized at S, and
multiply their denominators to get s₀ in S. Evaluating the finitely many relations in P
localized at s₀ gives elements whose images vanish in the localization at S. For each
relation, the fraction equality criterion supplies an element of S annihilating its
numerator. Multiply all these elements with s₀ to obtain s in S. All generator denominators
are invertible in P localized at s, and all relations vanish there. Thus the polynomial map
descends to C → P localized at s. The universal property gives the map from that principal
localization to the localization at S, and equality on the generators proves the composite
is the original map. This also covers an empty generator or relation list (empty product 1),
and a submonoid containing 0 (the resulting principal localization can be the zero ring). -/
theorem factors_through_principal_localization
    (R : Type u₁) (C : Type v₁) (P : Type w)
    [CommRing R] [CommRing C] [CommRing P]
    [Algebra R C] [Algebra R P] [Algebra.FinitePresentation R C]
    (S : Submonoid P) (g : C →ₐ[R] Localization S) :
    ∃ (s : S) (f : C →ₐ[R] Localization.Away (s : P))
      (k : Localization.Away (s : P) →ₐ[R] Localization S), k.comp f = g := by
  sorry

end Algebra
