/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Identity-open compactification comparisons

Source: main-20261015 blueprint, thm-sf-ambient-adjoint-class.proof.md,
identity-open specialization of the four-factor Hom chain
(blueprint: def-sf-closed-identity-open-comparison).

These are the specified identity-open adjunction identifications, constructed from
identity inverse image, adjunction uniqueness, and termwise descent. No comparison
with the etale/pro-etale site morphism or counit normalization is asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Remove identity etale extension by zero using its specified adjunction.
Source: identity-open specialization of thm-sf-ambient-adjoint-class.proof.md
(blueprint: def-sf-closed-identity-open-comparison). -/
def closedIdentityOpenEtaleComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
            (Etale.upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Remove identity pro-etale extension by zero using its specified adjunction.
Source: identity-open specialization of thm-sf-ambient-adjoint-class.proof.md
(blueprint: def-sf-closed-identity-open-comparison). -/
def closedIdentityOpenProEtaleComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
            (upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry.ProEtale
