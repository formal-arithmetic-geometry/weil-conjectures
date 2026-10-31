/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IsoAlgebraExtensionCondition
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # The coefficient-generic lisse Weil extension predicate

The canonical extension condition is kept coefficient-generic so its specializations
can be checked without expanding the concrete condensed coefficient ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- A lisse Weil extension with the canonical comparison for a commuting square.
Source: rem-dl-a1-conventions, unramifiedness paragraph.
(blueprint: def-dl-a1-coefficient-lisse-weil-extension).

Construction: quantify a lisse Weil module on the larger scheme, a proof that the
square commutes, and an underlying pullback isomorphism. Require its compatibility
with both Weil isomorphisms using the composition and equality comparisons of the
actual condensed pullback functors. This is exactly the usual extension condition
for every commutative condensed coefficient ring, including the zero ring.
-/
@[irreducible] def HasLisseWeilExtensionForCoefficient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U C : Scheme.{u}} (gU : U ≅ U) (gC : C ≅ C) (j : U ⟶ C)
    (F : CondensedRing.StrictWeil.WeilModule Λ gU) : Prop :=
  CategoryTheory.HasIsoAlgebraExtension (CondensedRing.upperStar Λ j)
    (CondensedRing.upperStar Λ gC.hom) (CondensedRing.upperStar Λ gU.hom)
    (gU.hom ≫ j = j ≫ gC.hom)
    (fun hcomm ↦ (CondensedRing.upperStarComp Λ gU.hom j).symm ≪≫
      CondensedRing.upperStarCongr Λ hcomm ≪≫ CondensedRing.upperStarComp Λ j gC.hom)
    (IsLisseCoefficientModule Λ) F

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
