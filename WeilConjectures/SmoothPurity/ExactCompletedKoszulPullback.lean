/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.CategoryTheory.RingedHomPullback.RingedHomComplexPullbackShiftSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SmoothPurity.CochainTensoratorExistence
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomComplexToSingle
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import WeilConjectures.AlgebraicGeometry.Constant.ConstantInverseImageSectionSupplement
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Hom.InjSurj
import WeilConjectures.ProperBaseChange.RingedCechKoszulDualKFlat
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Logic.Denumerable
import WeilConjectures.SmoothPurity.ExactProductFunctorRoosChainMaps
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulTowerComparisonSupplement

/-! # Koszul units under exact inverse image preserving products

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags
07A4 and 0941 (blueprint: lem-sfb-exact-completed-koszul-pullback).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
-- Keep the chosen localizations and completed coefficient limits from unfolding in proof search.
attribute [local irreducible] HasDerivedCategory.standard ConstantCompletion.completed
  ConstantCompletion.derivedPull
universe u w a b c d wA wB

namespace CategoryTheory
set_option backward.defeqAttrib.useBackward true
-- Cache the pointwise complex limit instances instead of rebuilding them at every projection.
attribute [local instance] complexTowerLimits complexNatProductLimits
  complexTowerLimit complexCountableProduct

variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{d} (ℕᵒᵖ ⥤ B)]

-- Extend the normalized Roos inclusion identity to all complexes.
omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)] in
omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{c} (ℕᵒᵖ ⥤ A)] in
end CategoryTheory

namespace CategoryTheory.ConstantCompletion
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
  (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v)) (adj : L ⊣ V)
  [PreservesFiniteLimits L]
  {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
  (c : F.rings.obj R ⟶ S) [IsIso c]

include V adj in
open SheafOfModules SheafOfModules.GeometricConstruction in
omit [PreservesFiniteLimits L] in
end CategoryTheory.ConstantCompletion

namespace CategoryTheory.ExactKoszulTransport
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
private abbrev Modules (O : Sheaf J CommRingCat.{u}) := ConstantCompletion.Mod O
open _root_.CategoryTheory.FlatScalarKoszul
  (derivedUnitNat derivedUnitNat_app unit_app_Q unit_naturality)

attribute [local irreducible] ringedKoszulTensor ringedKoszulDualTower
  ringedKoszulDiagram SheafOfModules.monoidalCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  RingedKoszulLimitPresentation.unit
  RingedKoszulLimitPresentation.unitOnComplex


section Transport
variable {E : Type u} [SmallCategory E] {K : GrothendieckTopology E}
  (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
  [HasDerivedCategory.{w} (ConstantCompletion.Mod R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ConstantCompletion.Mod R)]
  [HasDerivedCategory.{w} (ConstantCompletion.Mod S)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ConstantCompletion.Mod S)]
  (P : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod S) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  (r : ℕ) (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
  (a : Fin r → (S.obj ⋙ forget CommRingCat).sections)
  (DB : RingedKoszulLimitPresentation R r b)
  (DR : RingedKoszulLimitPresentation S r a)


omit [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)] in
omit [HasDerivedCategory (ConstantCompletion.Mod R)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod R)]
  [HasDerivedCategory (ConstantCompletion.Mod S)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod S)]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P)] in
set_option maxHeartbeats 800000 in
-- Normalize the dependent endpoints of the tower and localization comparisons.
end Transport
end CategoryTheory.ExactKoszulTransport

namespace CategoryTheory.ConstantCompletion

-- The concrete final calculation respects the protected choices and uses only naturality.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] pullDerivedIso pull RingedKoszulLimitPresentation.unit
  RingedKoszulLimitPresentation.completion Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors ringedKoszulTensor ringedKoszulDualTower
  ringedKoszulDiagram SheafOfModules.monoidalCategory

end CategoryTheory.ConstantCompletion
