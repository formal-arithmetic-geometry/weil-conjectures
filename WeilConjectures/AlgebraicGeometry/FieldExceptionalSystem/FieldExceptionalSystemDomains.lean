/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-domains).

Natural-number level n means exponent n+1. All morphisms are in ordinary derived
categories of strict systems, in the dependency's section-preserving coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] FieldShriekSystem.coefficientMap HasDerivedCategory.standard
attribute [local irreducible] supportEvaluation FieldShriekSystem.restrictionEvaluation
attribute [local irreducible] comparison normalized
attribute [local irreducible] scalarAssoc scalarUnit
attribute [local irreducible] reductionCtfCompactSupport
attribute [local irreducible] reductionCtfScalar scalarExtensionFunctor
attribute [local irreducible] reductionDirectImageComparison

/-- The dependency's normalized constructible full subcategory, with uniform bounds.
Source: blueprint (2), N_A(T) (blueprint: def-sp-field-exceptional-system-domains). -/
abbrev N (D : Models P) (E : Index P) (T : Scheme.{u}) :=
  (normalized P D E T).FullSubcategory

/-- Preservation and finite evaluation domains, all asserted as conclusions below.
As in the node, the schemes T range only over the source X and target Y of f.
Source: blueprint (1)--(2) (blueprint: def-sp-field-exceptional-system-domains). -/
structure Domains (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Prop where
  scalar : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}), (T = X ∨ T = Y) →
    ∀ (K : N P D E T), normalized P D F T ((D.scalars E F h T).T.obj K.obj)
  support : ∀ (E : Index P) (M : N P D E X), normalized P D E Y
    ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M.obj)
  finite : ∀ (E : Index P) (T : Scheme.{u}), (T = X ∨ T = Y) → ∀ (n : ℕ) (K : N P D E T),
    spFiniteConstructibleTor T (SpTowerShriek.R P.coefficients.l E.val n)
      ((SpTowerShriek.Ev P.coefficients.l E.val T n).obj K.obj)
  finiteScalar : ∀ (E F : Index P) (n m : ℕ)
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m) (T : Scheme.{u}), (T = X ∨ T = Y) →
    ∀ (K : spFiniteConstructibleTorCategory T (SpTowerShriek.R P.coefficients.l E.val n)),
    spFiniteConstructibleTor T (SpTowerShriek.R P.coefficients.l F.val m)
      ((scalarExtensionFunctor φ T).obj K.obj)

/-- Restriction of the actual scalar functor; it changes no ambient arrow.
Source: blueprint (2), C_T (blueprint: def-sp-field-exceptional-system-domains). -/
def scalar (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (a : Domains P D c) {E F : Index P} (h : E ≤ F) (T : Scheme.{u})
    (hT : T = X ∨ T = Y := by first | exact Or.inl rfl | exact Or.inr rfl) :
    N P D E T ⥤ N P D F T :=
  ObjectProperty.lift _ ((normalized P D E T).ι ⋙ (D.scalars E F h T).T)
    (a.scalar E F h T hT)

/-- Restriction of the same proper/open compact-support functor for every coefficient.
Source: blueprint (2), P_A (blueprint: def-sp-field-exceptional-system-domains). -/
def support (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : Domains P D c) (E : Index P) : N P D E X ⥤ N P D E Y :=
  ObjectProperty.lift _ ((normalized P D E X).ι ⋙
    SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c) (a.support E)

/-- Exact evaluation restricted to normalized constructible objects.
Source: blueprint (2), K_n (blueprint: def-sp-field-exceptional-system-domains). -/
def level (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (a : Domains P D c) (E : Index P) (T : Scheme.{u}) (n : ℕ)
    (hT : T = X ∨ T = Y := by first | exact Or.inl rfl | exact Or.inr rfl) :
    N P D E T ⥤ spFiniteConstructibleTorCategory T (SpTowerShriek.R P.coefficients.l E.val n) :=
  ObjectProperty.lift _ ((normalized P D E T).ι ⋙
    SpTowerShriek.Ev P.coefficients.l E.val T n) (a.finite E T hT n)


end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
