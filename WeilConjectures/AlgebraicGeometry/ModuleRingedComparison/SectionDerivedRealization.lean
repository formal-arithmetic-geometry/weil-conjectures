/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedTensorData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
/-! # Canonical derived section-module realization

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pd-section-derived-realization).

## Main definitions

- `derivedEquivalence`: localization of the fixed section equivalence.
- `derivedPullback`, `derivedPushforward`: actual ringed derived operations.
- `tensor`, `tensorComparison`, `qTensor`: the normalized K-flat tensor realization.
- `tensorPullComparison`: the uniquely specified ringed tensor-pullback map.
- `derivedExtension`, `derivedOpenAdjunction`: localized open extension and restriction.
- `derivedPullbackComposition`: localization of geometric pullback pasting.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option linter.mathlibStandardSet false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] sectionFunctorAdditive

attribute [local irreducible] ordinaryTensorComparison totalComparison tensorComparison
  Functor.mapDerivedCategory

attribute [local irreducible] tensor

attribute [local irreducible] CategoryTheory.Localization.Monoidal.tensorBifunctor
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

@[irreducible] private def uncurryTotalComparisonIso
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {TC : C ⥤ C ⥤ C} [TC.PreservesZeroMorphisms]
    [∀ M, (TC.obj M).PreservesZeroMorphisms]
    {TD : D ⥤ D ⥤ D} [TD.PreservesZeroMorphisms]
    [∀ M, (TD.obj M).PreservesZeroMorphisms]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q TC]
    [∀ P Q : CochainComplex D ℤ, P.HasMapBifunctor Q TD]
    (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj F).obj TC ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TD)
    [∀ M N, IsIso ((τ.app M).app N)] :
    Functor.uncurry.obj TC.map₂CochainComplex ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TD.map₂CochainComplex := by
  refine NatIso.ofComponents
    (fun K ↦ asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K.1 K.2)) ?_
  intro M N f
  let G := F.mapHomologicalComplex (.up ℤ)
  change G.map
      (HomologicalComplex.mapBifunctorMap f.1 (𝟙 M.2) TC (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 N.1) f.2 TC (.up ℤ)) ≫
      HomologicalComplex.mapBifunctorComparison τ (.up ℤ) N.1 N.2 =
    HomologicalComplex.mapBifunctorComparison τ (.up ℤ) M.1 M.2 ≫
      (HomologicalComplex.mapBifunctorMap (G.map f.1) (𝟙 (G.obj M.2)) TD (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (G.obj N.1)) (G.map f.2) TD (.up ℤ))
  have h₁ := HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) f.1 (𝟙 M.2)
  have h₂ := HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) (𝟙 N.1) f.2
  rw [Functor.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]
  dsimp only [G]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

@[irreducible] private def localization_single_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{v₂} D]
    (e : C ≌ D) [e.functor.Additive] (M : C) (N : D) (e₀ : e.functor.obj M ≅ N) :
    e.functor.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor D 0).obj N :=
  e.functor.mapDerivedCategoryFactors.app ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex e.functor (.up ℤ) 0).app M ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso e₀)

attribute [local instance] sectionOrdinaryTensorMap_isIso

@[irreducible] private def sectionTotalNatIso (X : Scheme.{u}) :
    internalTotalTensor Λ X ⋙ (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ) ≅
      ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).prod
        ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)) ⋙ totalTensor Λ X :=
  uncurryTotalComparisonIso (equivalence Λ X).functor (sectionOrdinaryTensorMap Λ X)

attribute [local irreducible] derivedEquivalence

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] derivedEquivalence

attribute [local irreducible] qTensor totalPullComparison

@[irreducible] private def totalPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    totalTensor Λ Y ⋙ (pullback Λ f).mapHomologicalComplex (.up ℤ) ≅
      (((pullback Λ f).mapHomologicalComplex (.up ℤ)).prod
        ((pullback Λ f).mapHomologicalComplex (.up ℤ))) ⋙ totalTensor Λ X :=
  uncurryTotalComparisonIso (pullback Λ f)
    (Functor.OplaxMonoidal.δNatTrans (pullback Λ f))

attribute [local irreducible] totalTensor

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
