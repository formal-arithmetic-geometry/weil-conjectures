/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Coherence of restriction and pullback for successive coefficient maps

Source: Stacks Project, Tags 03EL and 06YY.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry.Scheme

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
  comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
    (RX SX TX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY SY TY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (aX : RX ⟶ SX) (bX : SX ⟶ TX) (cX : RX ⟶ TX) (hX : aX ≫ bX = cX)
    (aY : RY ⟶ SY) (bY : SY ⟶ TY) (cY : RY ⟶ TY) (hY : aY ≫ bY = cY)
    (eR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RX ≅ RY)
    (eS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SX ≅ SY)
    (eT : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj TX ≅ TY)
    (ha : eR.hom ≫ aY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aX ≫ eS.hom)
    (hb : eS.hom ≫ bY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map bX ≫ eT.hom)
    (hc : eR.hom ≫ cY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map cX ≫ eT.hom)

end AlgebraicGeometry.Scheme
