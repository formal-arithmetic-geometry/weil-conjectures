/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum
public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum
import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBundle
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.CompactProjectionExchange
public import WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Vector.VectorTraceGeometricDescent
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityScalarCompatibility
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityScalarLineWitness
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.NormalizedIntegrationTensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorNormalizedUnitAdjunct
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorIntegrationCartesianTrace

/-! # Vector-bundle purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: cor-pur-vector-bundle-purity).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
attribute [local irreducible] AlgebraicGeometry.Etale.derivedTensorSymmetry

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

/-- Vector-bundle purity in the ordinary finite-coefficient realization.
The coefficient ring is arbitrary; in particular this includes every positive finite
quotient of a coefficient valuation ring. The scalar clause applies to every finite
coefficient homomorphism, including all quotient reductions and the unit object.
Source: latest blueprint sk-prop-an/cor-pur-vector-bundle-purity, paragraphs 1--2
(blueprint: lem-pur-ordinary-vector-bundle-purity-assembly). -/
def VectorBundlePurityConclusion (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  letI := (Etale.vectorIntegration_geometry B d F).1
  letI := (Etale.vectorIntegration_geometry B d F).2.1
  VectorPurityFunctorConclusion A (VectorBundleZeroSection.π B d F)
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B)
    (Etale.vectorIntegrationCoefficient A N hA B d F)
    (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom) ∧
  ∃ γ : VectorPurityGamma A N hA B d F,
    VectorPurityGammaNormalized A N hN hA B hB d F γ ∧
    (∀ K : Etale.DerivedCategoryModule A B, IsIso (γ.app K)) ∧
    PurityBaseChangeEquation A N hN hA B hB d F γ ∧
    PurityDirectSumEquation A N hN hA B hB d F γ ∧
    ∀ (A' : Type (u + 1)) [CommRing A'] [Finite A'] (φ : A →+* A'),
      PurityScalarReductionEquation φ N hN hA B hB d F γ

/-- Integration-normalized purity for arbitrary finite coefficients.

Source: latest blueprint sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraphs 1--2 (blueprint: lem-pur-ordinary-vector-bundle-purity-assembly).

Proof: the ordinary vector integration theorem gives the invertible normalized
adjunct and its unique unit orientation. Geometric trace descent, transposed under
the Brown adjunction, gives base change; the ordered two-block trace and composite
adjunction give direct sums. For scalar extension choose the uniquely root-normalized
Tate balancing, construct the target integration-normalized family independently,
and transpose scalar trace descent using the inverse compact-support comparison.
This gives the specified scalar mate equation, including its coefficient-unit
component. No flatness of the coefficient homomorphism is required. -/
theorem vectorBundlePurity (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    VectorBundlePurityConclusion A N hN hA B hB d F := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  obtain ⟨hpur, γ, hn, hi⟩ := vectorBundleNormalized A N hN hA B hB d F
  refine ⟨hpur, γ, hn, hi, ?_, ?_, ?_⟩
  · exact vectorIntegrationCounit_baseChange A N hN hA B hB d F γ hn hi
  · exact vectorIntegrationCounit_directSum A N hN hA B hB d F γ hn
  · intro A' _ _ φ
    obtain ⟨hA', c, hc⟩ := exists_purityScalarLineNormalization A N hN hA B hB A' φ
    obtain ⟨_, γm, hnm, hγm⟩ := vectorBundleNormalized A' N hN hA' B hB d F
    exact ⟨hA', c, γm, hnm, hc,
      scalarReduction_compatibility_of_witnesses A N hN hA B hB d F γ hn hi
        A' φ hA' c γm hnm hγm hc⟩

end WeilConjectures.PurityFiniteSetting
