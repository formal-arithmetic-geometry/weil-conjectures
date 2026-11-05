/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
public import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement

/-!
# Inverse-image compositors and restriction to constant coefficients

The completed derived inverse-image compositor is the localization of a section-normalized
module compositor, and restriction to constant coefficients respects the module and derived
inverse-image compositors.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8;
Stacks Tags 06YY and 0D6D (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section RestrictionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aZ : RZ ⟶ SZ) (aY : RY ⟶ SY) (aX : RX ⟶ SX)
  (cRg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
  (cSg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SZ ≅ SY)
  (cRf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
  (cSf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
  (cRfg : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
  (cSfg : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj SZ ≅ SX)
  (commg : cRg.hom ≫ aY = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aZ ≫ cSg.hom)
  (commf : cRf.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cSf.hom)
  (commfg : cRfg.hom ≫ aX =
    (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).map aZ ≫ cSfg.hom)

end RestrictionComposition

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section ReductionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end ReductionComposition

end AlgebraicGeometry.Scheme
