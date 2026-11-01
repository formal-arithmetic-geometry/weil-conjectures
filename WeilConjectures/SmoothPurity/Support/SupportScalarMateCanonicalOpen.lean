/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionCoordinates
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Comma.Arrow
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
/-- Canonical support mate factors through the invertible open scalar mate.
Source: Stacks 03DI, 0GL6 and 07A6; (blueprint: lem-exc-support-scalar-open-transport).
(blueprint: new-support-scalar-mate-canonical-open).
Proof: expand `sfCompactSupportRestriction`, apply `mateEquiv_vcomp`, and use the
normalized open counit square to identify the open mate with the open scalar iso;
remove that iso by `Arrow.isoMk`. -/
theorem supportScalarMate_canonical_open
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (Arrow.mk
      (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        (((mateEquiv
          (Scheme.proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := X) φ))
          aY).symm
          (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj K))) ≅
      properScalarMateArrow φ c.g
        (AlgebraicGeometry.ProEtale.scalarExtension φ c.Z)
        LY
        (Scheme.proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := c.Z) φ))
        aY
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)) := by
  sorry
end WeilConjectures
