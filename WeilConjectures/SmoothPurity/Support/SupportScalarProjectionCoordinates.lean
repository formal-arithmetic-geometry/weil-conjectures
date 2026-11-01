/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Proper scalar-mate arrow coordinate

This is the literal arrow-category presentation of the restricted proper scalar
mate. No comparison map or witness is chosen here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The restricted scalar transpose of the derived direct-image comparison.
Source: Stacks 07A6
(blueprint: def-exc-support-scalar-projection-coordinates). -/
abbrev properScalarMateArrow
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (LZ : proEtaleDerivedCategory Z A ⥤ proEtaleDerivedCategory Z B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Arrow (DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  Arrow.mk
    (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
      (((mateEquiv aZ aY).symm
        (TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction g φ).hom)).natTrans.app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj P)))

end WeilConjectures
