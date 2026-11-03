/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Proper comparison in the native condensed module categories

Source: the proper compact-support coincidence proposition, using the identity
compactification and its adjunction-normalized open unit.
(blueprint: prop-weil-proper-compact-coincidence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Extension along the identity is the identity through the specified open adjunction.
Source: identity-compactification normalization
(blueprint: prop-weil-proper-compact-coincidence). -/
def identityExtension (X : Scheme.{u}) : openImmersionLowerShriek Λ (𝟙 X) ≅ 𝟭 _ :=
  ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
    (upperStarId Λ X)).leftAdjointUniq Adjunction.id

/-- The canonical proper comparison for every condensed coefficient ring and every complex.
The chosen compactification is X --id--> X --a--> Y.
Source: Ra_! = Ra_* for proper a
(blueprint: prop-weil-proper-compact-coincidence). -/
def comparison {X Y : Scheme.{u}} (a : X ⟶ Y) [IsProper a] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper a) ≅
      (lowerStar Λ a).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso (identityExtension Λ X) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- Applying exact point sections and homology gives the comparison in every integer degree.
Source: H_c^i = H^i for proper a
(blueprint: prop-weil-proper-compact-coincidence). -/
def cohomology {X Y : Scheme.{u}} (a : X ⟶ Y) [IsProper a] (i : ℤ) :
    condensedRingCompactCohomology Λ (Compactification.ofIsProper a) i ≅
      condensedRingOrdinaryCohomology Λ a i :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (comparison Λ a)
      (condensedRingCoefficientSections Λ Y).rightDerivedFunctor)
    (DerivedCategory.homologyFunctor _ i)

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupProper
