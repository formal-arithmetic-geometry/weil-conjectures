/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Submission.WeilConjectures.Algebra.Homology.Strict.StrictProjectionLimitData
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Localization.Adjunction
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import Submission.WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Mathlib.CategoryTheory.Abelian.FunctorCategory

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite-free scalar extension and strict derived towers

Source: Stacks Project, algebraization.tex, Tag 0A0E (application); sites-cohomology.tex,
Tag 0941 (resolved Roos triangle); derived.tex, Tags 070I, 08BJ, 0BK6.
(blueprint: lem-weil-pbc-finite-free-strict-tower-transport).

The helpers specify canonical maps and their cochain factorizations. Positive
levels are indexed by `n : ℕ` meaning level `n + 1`. All complexes are unbounded.
The existing `StrictProjectionLimitData` packages the recorded total right derived limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v r w uA vA uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules

namespace CategoryTheory

/-- The ordinary inverse-limit functor on cochain complexes of strict towers.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
abbrev strictTowerLimitComplex (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical inclusion of the ordinary strict limit into the product of evaluations.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerLimitInclusion {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (strictTowerLimitComplex A).obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
  Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)

/-- Product comparison from a cochain tower to its derived evaluations, including the
specified evaluation factorization of the strict-limit interface.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerResolvedProduct {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj (∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n))) ⟶
      ∏ᶜ (fun n : ℕ ↦ (L.ev.obj (DerivedCategory.Q.obj I)).obj (op n)) :=
  piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ (L.evaluation.inv.app I).app (op n))

/-- Normalization of the whole Roos triangle on injective-term K-injective towers.
The last equation fixes the connecting arrow as the actual short-exact-sequence boundary.
It does not choose a completion of an abstract triangle.
Source: Stacks 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
def strictTowerRoosNormalized
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (L : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q) : Prop :=
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
    L.eta.app X ≫ L.p (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (strictTowerLimitInclusion X) ≫ strictTowerResolvedProduct L X) ∧
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    (∀ k : ℤ, Injective (I.X k)) →
    ∀ (h : strictTowerLimitInclusion I ≫
        towerTransitionEndomorphism
          (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) = 0)
      (hs : (ShortComplex.mk (strictTowerLimitInclusion I)
        (towerTransitionEndomorphism
          (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)) h).ShortExact),
      strictTowerResolvedProduct L I ≫ L.delta (DerivedCategory.Q.obj I) =
        DerivedCategory.triangleOfSESδ hs ≫ (L.eta.app I)⟦(1 : ℤ)⟧'

/-- Finite-free transport data with the normalized ordinary and derived comparisons,
all three Roos squares and the strict augmentation formula. `augmentation` quantifies
all maps to the ordinary limit, equivalently all compatible strict augmented towers.
Source: Stacks 0A0E, 0941 (blueprint: lem-weil-pbc-finite-free-strict-tower-transport). -/
structure FiniteFreeStrictTowerTransport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    [HasCountableProducts (DerivedCategory.{w} B)]
    (F : A ⥤ B) [F.Additive]
    (G : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B) [G.CommShift ℤ]
    (T : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (factors : DerivedCategory.Q ⋙ G ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (towerFactors : DerivedCategory.Q ⋙ T ≅
      (projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) where
  /-- The source total derived inverse limit with its functorial Roos triangles. -/
  source : StrictProjectionLimitData A DerivedCategory.Q DerivedCategory.Q
  /-- The target total derived inverse limit with its functorial Roos triangles. -/
  target : StrictProjectionLimitData B DerivedCategory.Q DerivedCategory.Q
  /-- The source total derived inverse limit is exact with its cochain shift. -/
  source_exact : ∃ (_ : source.L.CommShift ℤ), source.L.IsTriangulated
  /-- The target total derived inverse limit is exact with its cochain shift. -/
  target_exact : ∃ (_ : target.L.CommShift ℤ), target.L.IsTriangulated
  /-- Pin the source connecting arrow to the resolved short exact sequence. -/
  source_normalized : strictTowerRoosNormalized source
  /-- Pin the target connecting arrow to the resolved short exact sequence. -/
  target_normalized : strictTowerRoosNormalized target
  /-- The ordinary limit/tensor comparison. -/
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
    projectionPost (I := ℕᵒᵖ) F ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  /-- Its definition by ordinary limit projections. -/
  ordinary_normalized : ∀ X : ℕᵒᵖ ⥤ A, ordinary.hom.app X = limit.post X F
  /-- Canonical projection comparison for every countable family in D(A). -/
  products : ∀ M : ℕ → DerivedCategory.{w} A, IsIso (piComparison G M)
  /-- Exact termwise tensor commutes with derived evaluation. -/
  evaluation : T ⋙ target.ev ≅
    source.ev ⋙ projectionPost (I := ℕᵒᵖ) G
  /-- This is the evaluation comparison induced on actual cochain representatives. -/
  evaluation_normalized : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
    (target.ev.map (towerFactors.hom.app X)).app n ≫
        (target.evaluation.hom.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X)).app n ≫
        factors.inv.app (X.asFunctor.obj n) =
      (evaluation.hom.app (DerivedCategory.Q.obj X)).app n ≫
        G.map ((source.evaluation.hom.app X).app n)
  /-- The natural derived-limit comparison lambda. -/
  comparison : source.L ⋙ G ≅
    T ⋙ target.L
  /-- The defining total-derived comparison equation, for every complex. -/
  comparison_normalized : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    G.map (source.eta.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      factors.hom.app ((strictTowerLimitComplex A).obj X) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.eta.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.L.map (towerFactors.inv.app X)
  /-- The first square of the Roos triangles, with the canonical product comparison. -/
  roos_first : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (source.p X) ≫
        piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) =
      comparison.hom.app X ≫
        target.p (T.obj X)
  /-- The middle square: the projection comparison intertwines one minus shift. -/
  roos_middle : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (towerTransitionEndomorphism
        (fun n : ℕ ↦ (source.ev.obj X).map (homOfLE (Nat.le_succ n)).op)) ≫
        piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) =
      piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) ≫
        towerTransitionEndomorphism (fun n : ℕ ↦
          (target.ev.obj (T.obj X)).map
            (homOfLE (Nat.le_succ n)).op)
  /-- The last square, including the cochain-normalized shift comparison. -/
  roos_last : ∀ X : DerivedCategory.{w} (ℕᵒᵖ ⥤ A),
    G.map (source.delta X) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (source.L.obj X) ≫
        (comparison.hom.app X)⟦(1 : ℤ)⟧' =
      piComparison G (fun n : ℕ ↦ (source.ev.obj X).obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ (evaluation.inv.app X).app (op n)) ≫
        target.delta (T.obj X)
  /-- A strict augmentation is its ordinary-limit lift z. The equation is lambda C(z)=z'. -/
  augmentation : ∀ (M : CochainComplex A ℤ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
      (z : M ⟶ (strictTowerLimitComplex A).obj X),
    G.map (DerivedCategory.Q.map z ≫ source.eta.app X) ≫
        comparison.hom.app (DerivedCategory.Q.obj X) =
      factors.hom.app M ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map z ≫
          (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app X) ≫
        target.eta.app
          (((projectionPost (I := ℕᵒᵖ) F).mapHomologicalComplex (.up ℤ)).obj X) ≫
        target.L.map (towerFactors.inv.app X)
  /-- Naturality for a map (h,v) of entire augmented towers, including the source complex. -/
  augmented_naturality : ∀ (M N : CochainComplex A ℤ)
      (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
      (z : M ⟶ (strictTowerLimitComplex A).obj X)
      (t : N ⟶ (strictTowerLimitComplex A).obj Y)
      (h : M ⟶ N) (v : X ⟶ Y),
    z ≫ (strictTowerLimitComplex A).map v = h ≫ t →
      G.map (DerivedCategory.Q.map z ≫ source.eta.app X) ≫
          comparison.hom.app (DerivedCategory.Q.obj X) ≫
          target.L.map (T.map
            (DerivedCategory.Q.map v)) =
        G.map (DerivedCategory.Q.map h) ≫
          G.map (DerivedCategory.Q.map t ≫ source.eta.app Y) ≫
          comparison.hom.app (DerivedCategory.Q.obj Y)

private noncomputable def exactDerivedAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {F : A ⥤ B} {U : B ⥤ A} [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : F ⊣ U) :
    F.mapDerivedCategory ⊣ U.mapDerivedCategory := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (U.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q U.mapDerivedCategory := ⟨U.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    F.mapDerivedCategory U.mapDerivedCategory

end CategoryTheory

namespace SheafOfModules

open CategoryTheory.MonoidalCategory

open CategoryTheory.MonoidalCategory in
private noncomputable def tensorFreePowerIso
    {H : Type uA} [Category.{vA} H] [Abelian H] [MonoidalCategory H]
    [MonoidalPreadditive H] (R : H) (I : Type) [Finite I]
    (e : R ≅ 𝟙_ H) :
    tensorLeft (∐ (fun _ : I ↦ R)) ≅ Functor.const (Discrete I) ⋙ lim := by
  classical
  let : HasFiniteBiproducts H := HasFiniteBiproducts.of_hasFiniteProducts
  let i (M : H) : (∐ (fun _ : I ↦ R)) ⊗ M ≅ ∏ᶜ (fun _ : I ↦ M) :=
    (tensorRight M).mapIso (biproduct.isoCoproduct (fun _ : I ↦ R)).symm ≪≫
      (tensorRight M).mapBiproduct (fun _ : I ↦ R) ≪≫
      biproduct.mapIso (fun _ : I ↦ whiskerRightIso e M ≪≫ λ_ M) ≪≫
      biproduct.isoProduct _
  have hi (M : H) (j : I) : (i M).hom ≫ Pi.π _ j =
      ((biproduct.isoCoproduct (fun _ : I ↦ R)).inv ≫
        biproduct.π _ j ≫ e.hom) ▷ M ≫ (λ_ M).hom := by
    simp only [i, Iso.trans_hom, Category.assoc, biproduct.isoProduct_hom,
      Pi.lift_comp_π, biproduct.mapIso_hom, biproduct.map_π, Functor.mapBiproduct_hom,
      Functor.mapIso_hom, Iso.symm_hom, whiskerRightIso_hom,
      comp_whiskerRight]
    erw [biproduct.lift_π_assoc]
    rfl
  refine NatIso.ofComponents i ?_
  intro M N f
  change (∐ (fun _ : I ↦ R)) ◁ f ≫ (i N).hom =
    (i M).hom ≫ Limits.Pi.map (fun _ : I ↦ f)
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, hi, Limits.Pi.map_π]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  simpa only [Category.assoc] using congrArg (· ≫ f) (hi M j).symm

private theorem scalarRestrictionProperties
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J RingCat.{r}} (a : R ⟶ S) :
    (restrictScalars.{r} a).ReflectsIsomorphisms ∧
      PreservesLimitsOfSize.{r, r} (restrictScalars.{r} a) ∧
      PreservesColimitsOfSize.{r, r} (restrictScalars.{r} a) := by
  have hlim (A : Sheaf J RingCat.{r}) :
      PreservesLimitsOfSize.{r, r} (toSheaf.{r} A) :=
    by
      constructor
      intro K _
      exact ((CategoryTheory.moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).1
  have hcolim (A : Sheaf J RingCat.{r}) :
      PreservesColimitsOfSize.{r, r} (toSheaf.{r} A) :=
    by
      constructor
      intro K _
      exact ((CategoryTheory.moduleSheaves_colimits_forgetful A).2.2.2.2.2 K).2.1
  let : PreservesLimitsOfSize.{r, r} (toSheaf.{r} R) := hlim R
  let : PreservesLimitsOfSize.{r, r} (toSheaf.{r} S) := hlim S
  let : PreservesColimitsOfSize.{r, r} (toSheaf.{r} R) := hcolim R
  let : PreservesColimitsOfSize.{r, r} (toSheaf.{r} S) := hcolim S
  let : ReflectsLimitsOfSize.{r, r} (toSheaf.{r} R) :=
    reflectsLimits_of_reflectsIsomorphisms
  let : ReflectsColimitsOfSize.{r, r} (toSheaf.{r} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  let : PreservesLimitsOfSize.{r, r} (restrictScalars a ⋙ toSheaf.{r} R) :=
    inferInstanceAs (PreservesLimitsOfSize.{r, r} (toSheaf.{r} S))
  let : PreservesColimitsOfSize.{r, r} (restrictScalars a ⋙ toSheaf.{r} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{r, r} (toSheaf.{r} S))
  refine ⟨⟨?_⟩, preservesLimits_of_reflects_of_preserves _ (toSheaf.{r} R),
    preservesColimits_of_reflects_of_preserves _ (toSheaf.{r} R)⟩
  intro M N f hf
  have : IsIso ((toSheaf.{r} S).map f) :=
    inferInstanceAs (IsIso ((toSheaf.{r} R).map ((restrictScalars a).map f)))
  exact isIso_of_reflects_iso f (toSheaf.{r} S)

end SheafOfModules
