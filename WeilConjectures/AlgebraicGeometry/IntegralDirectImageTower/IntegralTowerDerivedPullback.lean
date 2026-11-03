/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullbackNormalizations
import WeilConjectures.SixFunctors.SequenceComparisonConstruction.NormalizedDerivedComparisonDescent
import WeilConjectures.CategoryTheory.Derived.DerivedResolvingPairRestriction
import WeilConjectures.CategoryTheory.SixFunctors.UnaryWhiskeringOfProduct
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

/-! # Normalized IntegralTowerDerivedPullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem kflat_iso {T : Scheme.{u}}
    {P Q : CochainComplex (spIntegralSectionModules l E T) ℤ}
    (e : P ≅ Q) (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := spIntegralSectionRing l E T) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) Q := by
  let := isMonoidal_W_independentCoefficients (spIntegralSectionRing l E T)
  let := monoidalCategory (spIntegralSectionRing l E T)
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients
    (spIntegralSectionRing l E T)
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (spIntegralSectionRing l E T)
  intro F hF
  let e' := ((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e
  have hh := hP F hF
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hh ⊢
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((HomotopyCategory.quotient _ _).mapIso e') hh

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem flat_iso {T : Scheme.{u}} {M N : spIntegralSectionModules l E T}
    (e : M ≅ N) (hM : IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T) M) :
    IsFlatOnSite (J := Scheme.ProEt.topology T) (R := spIntegralSectionRing l E T) N := by
  let := isMonoidal_W_independentCoefficients (spIntegralSectionRing l E T)
  let := monoidalCategory (spIntegralSectionRing l E T)
  have hM' := (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (spIntegralSectionRing l E T) M) hM
  have hN := (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.tensoringRight (spIntegralSectionModules l E T)).mapIso e) hM'
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (spIntegralSectionRing l E T) N).symm hN

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private def reductionCounit (s : Presentation l E) (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ derivedReduction l E s T ⟶
      (ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let := (s.towers T).hasDerived
  let E₀ := (spIntegralModuleEquivalence l E T).functor
  let V := (s.base.realization T).functor
  let R := (s.reduction T).red
  let a := Functor.whiskerRight
    (Functor.whiskerRight E₀.mapDerivedCategoryFactors.hom R) (realization l E s T).functor
  let b := Functor.whiskerRight
    (Functor.whiskerLeft (E₀.mapHomologicalComplex (.up ℤ)) (s.reduction T).counit)
    (realization l E s T).functor
  let c := Functor.whiskerLeft
    ((E₀ ⋙ (s.reduction T).ordinary).mapHomologicalComplex (.up ℤ))
    V.mapDerivedCategoryFactors.hom
  exact a ≫ b ≫ c

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem reduction_comparison_isIso (s : Presentation l E) (T : Scheme.{u})
    (P : CochainComplex (Modules l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
      (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (reductionComplexComparison l E s T P) := by
  let := (s.towers T).hasDerived
  let := s.base.realizationAdditive T
  have := (s.reduction T).computes _ hP
  unfold reductionComplexComparison
  infer_instance

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private def good (T : Scheme.{u}) : ObjectProperty (CochainComplex (Modules l E T) ℤ) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
    (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ i : ℤ, IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T)
      ((spIntegralModuleEquivalence l E T).functor.obj (P.X i))

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
