/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # Concrete maps for relative Mayer--Vietoris base change

Source: Stacks Project, Tags 08BV, 08HY and 0DJ9
(blueprint: def-pc-rf-mv-base-change-components).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The derived adjunction of exact open restriction, constructed from its underived
adjunction. Source: Stacks Project, Tag 08BV
(blueprint: def-pc-rf-mv-base-change-components). -/
@[irreducible] def mvOpenRestrictionAdjunction (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι :=
  let a : schemeOpenRestriction X U ⊣
      RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  a.mapDerivedCategoryRightDerivedAdjunction

/-- The comparison between pullback by an open immersion and exact restriction is
constructed by uniqueness of left adjoints; its unit and counit identities are those
of `Adjunction.leftAdjointUniq`. Source: Stacks Project, Tags 08DW and 079W
(blueprint: def-pc-rf-mv-base-change-components). -/
@[irreducible] def mvOpenPullbackIso (X : Scheme.{u}) (U : X.Opens) :
    derivedPullback U.ι ≅ (schemeOpenRestriction X U).mapDerivedCategory :=
  (mvDerivedPullbackAdjunction U.ι).leftAdjointUniq (mvOpenRestrictionAdjunction X U)

/-- Canonical pullback/restriction comparison. Unlike a witness of bare `Nonempty`,
this is constructed from the pinned pullback composition comparisons and the open
adjunctions. Source: Stacks Project, Tags 0D5S and 08DW
(blueprint: def-pc-rf-mv-base-change-components). -/
@[irreducible] def mvPullbackOpenRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    derivedPullback f ⋙ (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory ≅
      (schemeOpenRestriction Y V).mapDerivedCategory ⋙
        derivedPullback (f.resLE V (f ⁻¹ᵁ V) le_rfl) :=
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) a b
  Functor.isoWhiskerLeft (derivedPullback f) (mvOpenPullbackIso X (f ⁻¹ᵁ V)).symm ≪≫
    c (f ⁻¹ᵁ V).ι f ≪≫
    eqToIso (congrArg (fun k : (f ⁻¹ᵁ V).toScheme ⟶ Y => derivedPullback k)
      (Scheme.Hom.resLE_comp_ι f (U := V) le_rfl).symm) ≪≫
    (c (f.resLE V (f ⁻¹ᵁ V) le_rfl) V.ι).symm ≪≫
    Functor.isoWhiskerRight (mvOpenPullbackIso Y V)
      (derivedPullback (f.resLE V (f ⁻¹ᵁ V) le_rfl))

end AlgebraicGeometry
