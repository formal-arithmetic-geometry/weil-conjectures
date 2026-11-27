/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor

/-! # Realizations of localized integral morphisms

A rational module realization sends the localization of an integral morphism to the derived
scalar extension of that morphism, transported along the recorded object equalities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] {X : Scheme.{u}} [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- A realization sends the localization of an integral morphism to the derived scalar
extension of the morphism. -/
theorem RationalModuleRealization.map_rationalization (s : RationalModuleRealization l E X)
    {K L : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)} (f : K ⟶ L) :
    s.J.map ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      eqToHom (s.objects K) ≫
        (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).map f.hom ≫
          eqToHom (s.objects L).symm := by
  have h := s.fractions K L f 0
  simp only [pow_zero, inv_one, map_one, one_smul] at h
  exact h

end AlgebraicGeometry.Scheme
