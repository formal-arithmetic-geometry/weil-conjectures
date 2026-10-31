/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.AlgebraicGeometry.SfIdentityProjectionNormalization
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalDataSupplement
public import WeilConjectures.AlgebraicGeometry.SfGraphFirstProjectionSquare
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
public import WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
public import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
public import WeilConjectures.CategoryTheory.DerivedHomologyInjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.LargeHomSolutionSet
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
public import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
public import Mathlib.Algebra.Module.ULift
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
public import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
public import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import WeilConjectures.CategoryTheory.CountableCoproductsIdempotentComplete
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import WeilConjectures.CategoryTheory.CoproductsOfCopowers
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-! # Coherence of the finite small-etale projection transformation

Source: current blueprint, sec-six-functors/sk-prop-sf-pf-coherence,
statement and proof (blueprint: prop-sf-pf-coherence).

All inputs are in the unbounded small-etale derived categories with an arbitrary
finite commutative coefficient ring. The arrows are the canonical proper-counit/open
projection, compact-support exchange, and compactification comparisons. In particular,
reduction by every ideal is allowed without flatness or a Tor hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilConjectures

variable (Λ : Type (u + 1)) [CommRing Λ]

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

/-- Naturality in both inputs, as an equality of the actual projection components.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (a : K ⟶ K')
    {L L' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (b : L ⟶ L') :
    type_of% (projectionMapOfCompactification_naturality (ModuleCat.{u + 1} Λ) c a b) :=
  projectionMapOfCompactification_naturality (ModuleCat.{u + 1} Λ) c a b

/-- The specified common-refinement comparison intertwines the projection maps.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_compactification
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [Finite Λ]
    (c d : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of%
      (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c d K L) :=
  projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c d K L

/-- Proper coincidence through the specified compact-support/direct-image comparison.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_proper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) f K L) :=
  projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) f K L

/-- The displayed Cartesian square, including both tensor and pullback-square comparisons.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_baseChange_finite
    {X' X Y' Y : Scheme.{u}} [Finite Λ] {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq K L) :=
  projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq K L

/-- Tensor associativity of the canonical projection, before any reduction specialization.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_tensorAssociativity
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMapOfCompactification_assoc (ModuleCat.{u + 1} Λ) c K L N) :=
  projectionMapOfCompactification_assoc (ModuleCat.{u + 1} Λ) c K L N

/-- All-ideal finite reduction: the square is precisely part (1) of the reduction theorem.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_reduction_finite
    {X Y : Scheme.{u}} [Finite Λ] {f : X ⟶ Y} (c : Compactification f) (J : Ideal Λ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMapOfCompactification_constantSingle (ModuleCat.{u + 1} Λ) c
      (ModuleCat.of Λ (Λ ⧸ J)) K L) :=
  projectionMapOfCompactification_constantSingle (ModuleCat.{u + 1} Λ) c
      (ModuleCat.of Λ (Λ ⧸ J)) K L

/-- Composition for every compatible compactification tower, with its specified compositor.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_composition
    {X Y Z : Scheme.{u}} [Finite Λ] (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (projectionMapOfCompactification_tower_comp Λ f g d e K L) :=
  projectionMapOfCompactification_tower_comp Λ f g d e K L

/-- The identity projection becomes the identity under the canonical pullback and support units.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_identity
    (X : Scheme.{u}) [Finite Λ]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    type_of% (AlgebraicGeometry.Etale.SupportedTrace.identityProjectionNormalization Λ X K L) :=
  AlgebraicGeometry.Etale.SupportedTrace.identityProjectionNormalization Λ X K L

/-- The canonical compact-support compositors obey the associativity pentagon.
Source: current blueprint prop-sf-pf-coherence
(blueprint: prop-sf-pf-coherence). -/
theorem sixFunctorProjection_pentagon
    {X Y Z T : Scheme.{u}} [Finite Λ]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian T]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] :
    type_of% (unboundedEtaleLowerShriekCompIso_assoc Λ f g h) :=
  unboundedEtaleLowerShriekCompIso_assoc Λ f g h

end WeilConjectures
