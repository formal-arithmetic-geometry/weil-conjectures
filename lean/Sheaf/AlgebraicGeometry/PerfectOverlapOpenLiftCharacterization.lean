/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons

/-! # Characterizing equations for the canonical open lift -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The global lift is the pullback of the localization preimage.
Source: Stacks Project, Tag 08DW. This is the constructor equation of the
canonical lift. -/
theorem perfectOverlapOpenLiftObject_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) :
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    let W := (MorphismProperty.isomorphisms _).inverseImage rY
    letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
    letI : rY.EssSurj := Localization.essSurj rY W
    perfectOverlapOpenLiftObject f U A =
      (derivedPullback f).obj (rY.objPreimage A) := by
  intro rY W
  rfl

/-- The pinned open square for the restricted morphism.
Source: Stacks Project, Tag 08DW. -/
noncomputable def perfectOverlapOpenLiftBeta
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : schemeDerivedCategory Y) :
    (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory.obj
        ((derivedPullback f).obj M) ≅
      (derivedPullback (f ∣_ U)).obj
        ((schemeOpenRestriction Y U).mapDerivedCategory.obj M) := by
  exact (singleComplexOpenPullbackSquareIso f U (f ⁻¹ᵁ U) (f ∣_ U)
    (morphismRestrict_ι f U)).symm.app M

/-- The lift isomorphism is the fixed open-pullback square followed by the
localization preimage isomorphism. Source: Stacks Project, Tag 08DW.

Proof: The lift is defined by pulling back the chosen global preimage. Its
restriction to the inverse-image open is identified with restricted pullback
by `openPullbackRestrictionIso`. The preimage isomorphism then identifies the
restricted global object with `A`. These are exactly the two constructor
factors of `perfectOverlapOpenLiftIso`. -/
theorem perfectOverlapOpenLiftIso_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) :
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    let W := (MorphismProperty.isomorphisms _).inverseImage rY
    letI : rY.IsLocalization W := schemeDerivedOpenRestriction_isLocalization Y U
    letI : rY.EssSurj := Localization.essSurj rY W
    let M := rY.objPreimage A
    let α := rY.objObjPreimageIso A
    perfectOverlapOpenLiftIso f U A =
      perfectOverlapOpenLiftBeta f U M ≪≫
        (derivedPullback (f ∣_ U)).mapIso α := by
  intro rY W M α
  unfold perfectOverlapOpenLiftIso perfectOverlapOpenLiftBeta
  rfl

end AlgebraicGeometry
