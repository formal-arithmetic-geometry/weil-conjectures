/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenLiftCharacterization

/-! # Component equations for the canonical open lift -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The canonical beta component is the inverse pinned open square.
Source: Stacks Project, Tag 08DW. -/
theorem perfectOverlapOpenLiftBeta_hom_square
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : schemeDerivedCategory Y) :
    (perfectOverlapOpenLiftBeta f U M).hom =
      (singleComplexOpenPullbackSquareIso f U (f ⁻¹ᵁ U) (f ∣_ U)
        (morphismRestrict_ι f U)).inv.app M := by
  unfold perfectOverlapOpenLiftBeta
  rfl

/-- The inverse beta component is the forward pinned open square.
Source: Stacks Project, Tag 08DW. -/
theorem perfectOverlapOpenLiftBeta_inv_square
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : schemeDerivedCategory Y) :
    (perfectOverlapOpenLiftBeta f U M).inv =
      (singleComplexOpenPullbackSquareIso f U (f ⁻¹ᵁ U) (f ∣_ U)
        (morphismRestrict_ι f U)).hom.app M := by
  unfold perfectOverlapOpenLiftBeta
  rfl

/-- The forward lift map is the beta square followed by the image of the
chosen localization preimage isomorphism. Source: Stacks Project, Tag 08DW. -/
theorem perfectOverlapOpenLiftIso_hom_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) :
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    let W := (MorphismProperty.isomorphisms _).inverseImage rY
    letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
    letI : rY.EssSurj := Localization.essSurj rY W
    let M := rY.objPreimage A
    let α := rY.objObjPreimageIso A
    (perfectOverlapOpenLiftIso f U A).hom =
      (perfectOverlapOpenLiftBeta f U M).hom ≫
        (derivedPullback (f ∣_ U)).map α.hom := by
  intro rY W M α
  have h := congrArg Iso.hom (perfectOverlapOpenLiftIso_eq f U A)
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using h

/-- The inverse lift map transports the localization preimage isomorphism
backwards, then uses the inverse beta square. Source: Stacks Project,
Tag 08DW. -/
theorem perfectOverlapOpenLiftIso_inv_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) :
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    let W := (MorphismProperty.isomorphisms _).inverseImage rY
    letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
    letI : rY.EssSurj := Localization.essSurj rY W
    let M := rY.objPreimage A
    let α := rY.objObjPreimageIso A
    (perfectOverlapOpenLiftIso f U A).inv =
      (derivedPullback (f ∣_ U)).map α.inv ≫
        (perfectOverlapOpenLiftBeta f U M).inv := by
  intro rY W M α
  have h := congrArg Iso.inv (perfectOverlapOpenLiftIso_eq f U A)
  simpa only [Iso.trans_inv, Functor.mapIso_inv] using h

end AlgebraicGeometry
