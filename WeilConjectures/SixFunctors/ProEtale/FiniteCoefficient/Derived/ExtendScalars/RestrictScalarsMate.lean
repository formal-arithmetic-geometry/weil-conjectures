/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Derived pullback, extension and restriction of scalars

Let `S` be an algebra over a noetherian commutative ring `R` and `g : Z ⟶ Y` a morphism of
schemes. The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived scalar extension `Ψ = - ⊗ᴸ_R S` with the
derived pullback (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`) and the
commutation `Lg^* Res ≅ Res Lg^*` of restriction of scalars with the derived pullback
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`) are mates along the
adjunctions `Ψ ⊣ Res` (blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The commutation `Lg^* Ψ ≅ Ψ Lg^*` of derived scalar extension with the derived pullback is
the mate, along the adjunctions `Ψ ⊣ Res`, of the commutation `Lg^* Res ≅ Res Lg^*` of
restriction of scalars with the derived pullback (blueprint `thm-trf-finite-coefficient-map`). -/
theorem mateEquiv_leftDerivedUpperStarExtendScalarsIso_inv :
    mateEquiv (leftDerivedSheafExtendScalarsAdjunction R S Y)
        (leftDerivedSheafExtendScalarsAdjunction R S Z)
        (leftDerivedUpperStarExtendScalarsIso R S g).inv =
      (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) g).hom := by
  sorry

end AlgebraicGeometry.ProEtale
