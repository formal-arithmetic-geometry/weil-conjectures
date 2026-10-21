/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q41 and Q2
-/
module

public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.RingedCoefficientCounitPresentations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Ordinary comparison data for arbitrary sheaf slices

The ordinary ringed square and its canonical normalizations, separated from the
unbounded derived comparison. Source: Stacks Project, Tags 04IF and 04H1.
(blueprint: def-sbc-ringed-sheaf-slice-ordinary-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory

/-- The canonical element restriction commutes with forgetting the module structure.
Source: Stacks 04IE, sectionwise restriction
(blueprint: def-sbc-ringed-sheaf-slice-ordinary-data). -/
def sheafSliceUnderlyingRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    elementModulePullback.{u, u} (localCoefficientRings R) A ⋙
        underlying (presentationElementRing R A) ≅
      underlying R ⋙ elementSheafPullback A :=
  Iso.refl _

/-- The canonical localization identification, fixed on every section of every fibre.
The projection from `A × F` is the second projection, since `Over.star A` uses the first
projection as its structure map. Source: Stacks 0791, 04H1 and 04IF
(blueprint: def-sbc-ringed-sheaf-slice-ordinary-data). -/
structure SheafSliceSetLocalization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A : Sheaf J (Type u)}
    (S : RingedSheafSliceAdjunctionData R A) where
  iso : Over.star A ⋙ S.fibreEquivalence.inverse ≅ elementSheafPullback A
  sections : ∀ (F : Sheaf J (Type u)) (U : Cᵒᵖ) (s : A.obj.obj U)
    (x : (S.fibreEquivalence.inverse.obj ((Over.star A).obj F)).obj.obj
      (elementObj A U s)),
    (iso.hom.app F).hom.app (elementObj A U s) x =
      (prod.snd : A ⨯ F ⟶ F).hom.app U
        (((S.fibre_iso.hom.app ((Over.star A).obj F)).app (elementObj A U s) x).val)

/-- The normalized geometric and ordinary module square, before resolution preservation.
Source: Stacks Project, Modules on Sites, Tag 04IF; Sites, Tag 04H1.
(blueprint: def-sbc-ringed-sheaf-slice-ordinary-data). -/
structure RingedSheafSliceSquare
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u)) where
  sourceSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A)
  targetSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A
  sourceLocalization : SheafSliceSetLocalization sourceSlice
  targetLocalization : SheafSliceSetLocalization targetSlice
  slice : RingedToposMorphism
    (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
    (localCoefficientRings (presentationElementRing RY A))
  sliceInverse : slice.inverse ≅ targetSlice.fibreEquivalence.functor ⋙
    Over.post f.inverse ⋙ sourceSlice.fibreEquivalence.inverse
  starComparison : Over.star A ⋙ Over.post f.inverse ≅
    f.inverse ⋙ Over.star (f.inverse.obj A)
  starComparison_formula : ∀ F : Sheaf K (Type u),
    (starComparison.hom.app F).left = prodComparison f.inverse A F
  sets : elementSheafPullback A ⋙ slice.inverse ≅
    f.inverse ⋙ elementSheafPullback (f.inverse.obj A)
  sets_formula : ∀ F : Sheaf K (Type u), sets.hom.app F =
    slice.inverse.map (targetLocalization.iso.inv.app F) ≫
      sliceInverse.hom.app (targetSlice.fibreEquivalence.inverse.obj ((Over.star A).obj F)) ≫
      sourceSlice.fibreEquivalence.inverse.map ((Over.post f.inverse).map
        (targetSlice.fibreEquivalence.counitIso.hom.app ((Over.star A).obj F))) ≫
      sourceSlice.fibreEquivalence.inverse.map (starComparison.hom.app F) ≫
      sourceLocalization.iso.hom.app (f.inverse.obj F)
  structural : sets.hom.app ((sheafCompose K (forget RingCat)).obj
      (localCoefficientRings RY)) ≫
      (elementSheafPullback (f.inverse.obj A)).map f.ringMap = slice.ringMap
  pullback : modules RY ⥤ modules RX
  [pullbackAdditive : pullback.Additive]
  ordinaryAdjunction : pullback ⊣ f.modules
  slicePullback : ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A) ⥤
    ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A))
  [slicePullbackAdditive : slicePullback.Additive]
  sliceOrdinaryAdjunction : slicePullback ⊣ slice.modules
  sigma : elementModulePullback.{u, u} (localCoefficientRings RY) A ⋙ slicePullback ≅
    pullback ⋙ elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)
  delta : f.modules ⋙ elementModulePullback.{u, u} (localCoefficientRings RY) A ≅
    elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A) ⋙ slice.modules
  ordinary_mate :
    (mateEquiv ordinaryAdjunction sliceOrdinaryAdjunction
      (TwoSquare.mk _ _ _ _ sigma.hom)).natTrans = delta.hom
  delta_underlying : ∀ E : modules RX,
    (underlying (presentationElementRing RY A)).map (delta.hom.app E) ≫
      slice.underlying.hom.app
        ((elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).obj E) =
    (sheafSliceUnderlyingRestriction RY A).hom.app (f.modules.obj E) ≫
      (elementSheafPullback A).map (f.underlying.hom.app E) ≫
      (mateEquiv f.adj slice.adj (TwoSquare.mk _ _ _ _ sets.hom)).natTrans.app
        ((underlying RX).obj E) ≫
      slice.direct.map ((sheafSliceUnderlyingRestriction RX (f.inverse.obj A)).inv.app E)

/-- The canonical ordinary ringed square, exact restrictions and resolution preservation.

This is output data, not an assumption on the ringed morphism. Ordinary pullbacks are
specified as left adjoints to the supplied induced module direct images; this determines
them with their adjunctions up to the unique adjunction-preserving isomorphism. The ordinary
comparison is fixed as the mate of the geometric direct-image identification. The derived
output proposition below uses this ordinary output as its parameter.

Source: Stacks 04IF, 04H1, 0G7E, 08FI, 07A6, 07A7 and 09T5
(blueprint: def-sbc-ringed-sheaf-slice-ordinary-data). -/
structure RingedSheafSliceOrdinaryComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u)) where
  sourceSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A)
  targetSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A
  sourceLocalization : SheafSliceSetLocalization sourceSlice
  targetLocalization : SheafSliceSetLocalization targetSlice
  slice : RingedToposMorphism
    (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
    (localCoefficientRings (presentationElementRing RY A))
  sliceInverse : slice.inverse ≅ targetSlice.fibreEquivalence.functor ⋙
    Over.post f.inverse ⋙ sourceSlice.fibreEquivalence.inverse
  starComparison : Over.star A ⋙ Over.post f.inverse ≅
    f.inverse ⋙ Over.star (f.inverse.obj A)
  starComparison_formula : ∀ F : Sheaf K (Type u),
    (starComparison.hom.app F).left = prodComparison f.inverse A F
  sets : elementSheafPullback A ⋙ slice.inverse ≅
    f.inverse ⋙ elementSheafPullback (f.inverse.obj A)
  sets_formula : ∀ F : Sheaf K (Type u), sets.hom.app F =
    slice.inverse.map (targetLocalization.iso.inv.app F) ≫
      sliceInverse.hom.app (targetSlice.fibreEquivalence.inverse.obj ((Over.star A).obj F)) ≫
      sourceSlice.fibreEquivalence.inverse.map ((Over.post f.inverse).map
        (targetSlice.fibreEquivalence.counitIso.hom.app ((Over.star A).obj F))) ≫
      sourceSlice.fibreEquivalence.inverse.map (starComparison.hom.app F) ≫
      sourceLocalization.iso.hom.app (f.inverse.obj F)
  structural : sets.hom.app ((sheafCompose K (forget RingCat)).obj
      (localCoefficientRings RY)) ≫
      (elementSheafPullback (f.inverse.obj A)).map f.ringMap = slice.ringMap
  pullback : modules RY ⥤ modules RX
  [pullbackAdditive : pullback.Additive]
  ordinaryAdjunction : pullback ⊣ f.modules
  slicePullback : ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A) ⥤
    ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A))
  [slicePullbackAdditive : slicePullback.Additive]
  sliceOrdinaryAdjunction : slicePullback ⊣ slice.modules
  sigma : elementModulePullback.{u, u} (localCoefficientRings RY) A ⋙ slicePullback ≅
    pullback ⋙ elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)
  delta : f.modules ⋙ elementModulePullback.{u, u} (localCoefficientRings RY) A ≅
    elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A) ⋙ slice.modules
  ordinary_mate :
    (mateEquiv ordinaryAdjunction sliceOrdinaryAdjunction
      (TwoSquare.mk _ _ _ _ sigma.hom)).natTrans = delta.hom
  delta_underlying : ∀ E : modules RX,
    (underlying (presentationElementRing RY A)).map (delta.hom.app E) ≫
      slice.underlying.hom.app
        ((elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).obj E) =
    (sheafSliceUnderlyingRestriction RY A).hom.app (f.modules.obj E) ≫
      (elementSheafPullback A).map (f.underlying.hom.app E) ≫
      (mateEquiv f.adj slice.adj (TwoSquare.mk _ _ _ _ sets.hom)).natTrans.app
        ((underlying RX).obj E) ≫
      slice.direct.map ((sheafSliceUnderlyingRestriction RX (f.inverse.obj A)).inv.app E)
  [targetRestrictionAdditive :
    (elementModulePullback.{u, u} (localCoefficientRings RY) A).Additive]
  [sourceRestrictionAdditive :
    (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).Additive]
  [targetRestrictionLimits :
    PreservesFiniteLimits (elementModulePullback.{u, u} (localCoefficientRings RY) A)]
  [sourceRestrictionLimits :
    PreservesFiniteLimits
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))]
  [targetRestrictionColimits :
    PreservesFiniteColimits (elementModulePullback.{u, u} (localCoefficientRings RY) A)]
  [sourceRestrictionColimits :
    PreservesFiniteColimits
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))]
  targetKFlat : ∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing RY A)
        ((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := presentationElementRing RY A)
        (((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T).X n)
  sourceKInjective : ∀ I : CochainComplex (modules RX) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective ((onComplex
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))).obj I)
attribute [instance] RingedSheafSliceOrdinaryComparison.pullbackAdditive
  RingedSheafSliceOrdinaryComparison.slicePullbackAdditive

end CategoryTheory
