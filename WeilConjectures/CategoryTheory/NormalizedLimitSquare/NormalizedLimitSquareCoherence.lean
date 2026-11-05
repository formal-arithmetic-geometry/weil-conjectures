/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RoosAdjunctionUnit.RoosAdjunctionUnitCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Localization.Predicate
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement

/-! # Normalized inverse-limit comparisons respect an exact functor square

Source: the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md;
projection and conjugation calculation in the DAG proof
(blueprint: lem-cbc-normalized-limit-square-coherence).

The records package conclusions of the theorem, rather than extra hypotheses.
The underlying complex is the existing `roosF`. Its existing signed `coordinates`
give (x,y) in degrees (q,q-1), with d(x,y)=(dx,(1-s)x-dy).
All comparisons use that same model at a shared corner.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option linter.all false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RoosAdjunctionUnit

namespace CategoryTheory.NormalizedLimitSquare

attribute [local irreducible] roosF roosχ roosι DerivedCategory.Q
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] roosAdditiveComparison coordinates

universe u v w u' v' w' u0 v0 w0 u1 v1 w1 u2 v2 w2 u3 v3 w3
universe c0 d0 r0 c1 d1 r1 c2 d2 r2 c3 d3 r3

section Edge
variable {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)]
  {LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A}
  {LB : DerivedCategory.{w'} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w'} B}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}

/-- The canonical derived augmentation obtained from the strict limit cone.
Source: the strict augmentation clause of Stacks 0941 and
(blueprint: lem-cbc-normalized-limit-square-coherence).
The named map keeps repeated limit-cone conversions out of the coherence record. -/
@[irreducible] def augmentation
    {T : ℕᵒᵖ ⥤ CochainComplex A ℤ} {Z : DerivedCategory.{w} A}
    (c : Cone T) (unit : DerivedCategory.Q.obj (limit T) ⟶ Z) :
    DerivedCategory.Q.obj c.pt ⟶ Z :=
  DerivedCategory.Q.map (limit.lift T c) ≫ unit

end Edge

section Square
variable {A0 : Type u0} [Category.{v0} A0] [Abelian A0]
  [HasCountableProducts A0] [HasLimitsOfShape ℕᵒᵖ A0]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)]
variable {A1 : Type u1} [Category.{v1} A1] [Abelian A1]
  [HasCountableProducts A1] [HasLimitsOfShape ℕᵒᵖ A1]
  [HasDerivedCategory.{w1} A1] [HasDerivedCategory.{w1} (ℕᵒᵖ ⥤ A1)]
variable {A2 : Type u2} [Category.{v2} A2] [Abelian A2]
  [HasCountableProducts A2] [HasLimitsOfShape ℕᵒᵖ A2]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{w2} (ℕᵒᵖ ⥤ A2)]
variable {A3 : Type u3} [Category.{v3} A3] [Abelian A3]
  [HasCountableProducts A3] [HasLimitsOfShape ℕᵒᵖ A3]
  [HasDerivedCategory.{w3} A3] [HasDerivedCategory.{w3} (ℕᵒᵖ ⥤ A3)]
variable (F : A0 ⥤ A1) (G : A1 ⥤ A3) (H : A0 ⥤ A2) (K : A2 ⥤ A3)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

omit [HasCountableProducts A0] [HasCountableProducts A1]
  [HasCountableProducts A2] [HasCountableProducts A3]
  [HasLimitsOfShape ℕᵒᵖ A0] [HasLimitsOfShape ℕᵒᵖ A1]
  [HasLimitsOfShape ℕᵒᵖ A2] [HasLimitsOfShape ℕᵒᵖ A3]
  [HasDerivedCategory.{w0} A0] [HasDerivedCategory.{w1} A1]
  [HasDerivedCategory.{w2} A2] [HasDerivedCategory.{w3} A3]
  [HasDerivedCategory.{w0} (ℕᵒᵖ ⥤ A0)] [HasDerivedCategory.{w1} (ℕᵒᵖ ⥤ A1)]
  [HasDerivedCategory.{w2} (ℕᵒᵖ ⥤ A2)] [HasDerivedCategory.{w3} (ℕᵒᵖ ⥤ A3)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K] in
/-- Termwise square map, with its two-step tower functors explicitly typed.
Source: naturality of the given square
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
@[irreducible] def towerMap (e : F ⋙ G ⟶ H ⋙ K) :
    towerComplex F ⋙ towerComplex G ⟶ towerComplex H ⋙ towerComplex K :=
  NatTrans.mapHomologicalComplex
    ((Functor.whiskeringRight ℕᵒᵖ A0 A3).map e) (.up ℤ)

variable (L0 : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0) ⥤ DerivedCategory.{w0} A0)
  (eta0 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L0)
variable (L1 : DerivedCategory.{w1} (ℕᵒᵖ ⥤ A1) ⥤ DerivedCategory.{w1} A1)
  (eta1 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L1)
variable (L2 : DerivedCategory.{w2} (ℕᵒᵖ ⥤ A2) ⥤ DerivedCategory.{w2} A2)
  (eta2 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L2)
variable (L3 : DerivedCategory.{w3} (ℕᵒᵖ ⥤ A3) ⥤ DerivedCategory.{w3} A3)
  (eta3 : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L3)

end Square

end CategoryTheory.NormalizedLimitSquare
