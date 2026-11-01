/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-! # Canonical ordinary source and counit coordinates

This is the unchanged source-descent and counit construction from
AffineOrderedIntegrationTransposes, isolated so its rank-zero and successor
lemmas can be stated without an import cycle.
Source: current blueprint, projection-purity agreement proof, final paragraph.
(blueprint: def-pur-affine-ordered-counit-data).
-/

@[expose] public section
set_option autoImplicit false

/-! # Ordered affine integration transposes

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement.proof.md, final paragraph
(blueprint: lem-pur-affine-ordered-integration-transposes).
- Canonical affine integration is transported from the ordered ordinary counit.
- Its coefficient transpose is compared with the recorded affine-space recursion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.mapDerivedCategory DerivedCategory.singleFunctors

attribute [local irreducible] projectionMapOfCompactification
attribute [local semireducible] AffineLinePurity.proSourceObject
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_plus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((Etale.ordinaryFinitePullback A f).obj K) := by
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K).symm
    (((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj ⟨K, hK⟩).property)

private theorem flat_tensor_shift_plus
    {B : Type*} [Category B] [Abelian B] [IsGrothendieckAbelian B]
    [HasDerivedCategory B] [MonoidalCategory B] [MonoidalPreadditive B]
    [BraidedCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (L : B) (hL : ObjectProperty.flat L) (K : DerivedCategory B)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      (K ⊗ ((DerivedCategory.singleFunctor B 0).obj L)⟦(2 : ℤ)⟧) := by
  let := Classical.choice (DerivedCategory.nonempty_braidedCategory B)
  obtain ⟨a, ha⟩ := hK
  have : K.IsGE a := ha
  let S := (DerivedCategory.singleFunctor B 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hL
  have : (S ⊗ K).IsGE (0 + a) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeIn ht K a
  have hs : DerivedCategory.TStructure.t.plus ((S ⊗ K)⟦(2 : ℤ)⟧) :=
    ⟨0 + a - 2, DerivedCategory.TStructure.t.isGE_shift _ (0 + a) 2
      (0 + a - 2) (by omega)⟩
  have hs' : DerivedCategory.TStructure.t.plus (S⟦(2 : ℤ)⟧ ⊗ K) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (((MonoidalCategory.tensorRight K).commShiftIso (2 : ℤ)).app S).symm hs
  exact DerivedCategory.TStructure.t.plus.prop_of_iso (β_ _ _) hs'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorLine_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (K : Etale.DerivedCategoryModule A T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus
      ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
        ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)).obj K) := by
  let L := Scheme.finiteEtaleTateLine T N A hA
  have hInv : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line T N hN hInv A hA 1).2.2.1
  exact flat_tensor_shift_plus L hf K hK

universe w

/-- Compose a source isomorphism with the inverse of a specified identity-functor iso.
This categorical cache avoids expanding sheaf tensor units during endpoint inference.
Source: identity normalization
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def identityPullbackSource {Cat : Type v} [Category.{w} Cat]
    (F : Cat ⥤ Cat) (eF : F ≅ 𝟭 Cat) {K L : Cat} (e : K ≅ L) : K ≅ F.obj L :=
  e ≪≫ (eF.app L).symm

private theorem ordinaryGenericZeroTensorTrace_isIso
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (Y : Scheme.{u}) (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    IsIso ((Etale.ordinaryDerivedTensorTrace B Y
      (𝟙 ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology B).obj (𝟙_ B))))).app K) := by
  unfold Etale.ordinaryDerivedTensorTrace
  dsimp only [NatTrans.comp_app]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical tensor of the identity coefficient trace is invertible.
Source: the right unit constraint
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: ordinaryFiniteTensorTrace_app identifies this component with tensor of the
identity followed by the canonical right unitor. The first map is identity and the
second is an isomorphism, hence their composite is invertible. -/
theorem ordinaryZeroTensorTrace_isIso (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (K : Etale.DerivedCategoryModule A Y) :
    IsIso ((Etale.ordinaryFiniteTensorTrace A Y (𝟙 (Etale.ordinaryFiniteUnit A Y))).app K) := by
  exact ordinaryGenericZeroTensorTrace_isIso (ModuleCat.{u + 1} A) Y K

/-- The rank-zero canonical ordinary source normalization.
Source: identity pullback and the tensor of the identity trace
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryDescentZeroRaw (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (K : Etale.DerivedCategoryModule A Y) :=
  letI := ordinaryZeroTensorTrace_isIso A Y K
  identityPullbackSource (Etale.ordinaryFinitePullback A (𝟙 Y))
    (Etale.affineLinearPullbackId A Y)
    (asIso ((Etale.ordinaryFiniteTensorTrace A Y (𝟙 (Etale.ordinaryFiniteUnit A Y))).app K)).symm

/-- One explicit ordinary source descent step: line descent, Tate pullback, tensor
reassociation, and inverse-image composition, in that order.
Source: canonical ordered source identification
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryDescentStepRaw (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) (d : ℕ)
    (e : (Etale.affineTraceRight A N hA Y d).obj K ≅
      (Etale.ordinaryFinitePullback A (affineTraceProjection Y d)).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
          (Etale.affineLinearBaseCoefficient A N hA Y d))) :=
    Etale.affineLinearLineDescent A N hA t (affineTraceTower Y d)
        (affineTraceInvertible N Y hY d) _ ≪≫
      (Etale.ordinaryFinitePullback A
        (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)).mapIso
        (Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d)
          e
          (Etale.ordinaryFiniteShiftedLinePullback A N hA t
            (affineTraceProjection Y d) hY).symm ≪≫
          (Etale.ordinaryFiniteTensorPullback A (affineTraceProjection Y d)
            (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
              (Etale.affineLinearBaseCoefficient A N hA Y d))
            ((Etale.ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)).symm ≪≫
          (Etale.ordinaryFinitePullback A (affineTraceProjection Y d)).mapIso
            (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) Y K _ _)) ≪≫
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} (affineTraceTower Y d) ↘ affineTraceTower Y d)
        (affineTraceProjection Y d)).symm.app _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem dependent_rec_unique {E : ℕ → Type*} (e₀ : E 0)
    (step : ∀ n, E n → E (n + 1)) :
    ∃! e : ∀ n, E n, e 0 = e₀ ∧ ∀ n, e (n + 1) = step n (e n) := by
  let e := Nat.rec (motive := E) e₀ step
  refine ⟨e, ⟨rfl, fun _ ↦ rfl⟩, ?_⟩
  intro e' he'
  funext n
  induction n with
  | zero => exact he'.1
  | succ n ih => rw [he'.2, ih]

private theorem iso_rec_unique {Cat : ℕ → Type*} [∀ n, Category (Cat n)]
    (K L : ∀ n, Cat n) (e₀ : K 0 ≅ L 0)
    (step : ∀ n, (K n ≅ L n) → (K (n + 1) ≅ L (n + 1))) :
    ∃! e : ∀ n, K n ≅ L n,
      HEq (e 0).hom e₀.hom ∧ ∀ n, HEq (e (n + 1)).hom (step n (e n)).hom := by
  obtain ⟨e, he, huniq⟩ := dependent_rec_unique e₀ step
  refine ⟨e, ⟨?_, ?_⟩, ?_⟩
  · exact he.1 ▸ HEq.rfl
  · intro n
    exact he.2 n ▸ HEq.rfl
  · intro e' he'
    exact huniq e' ⟨Iso.ext (eq_of_heq he'.1),
      fun n ↦ Iso.ext (eq_of_heq (he'.2 n))⟩

/-- The explicit recursive source maps determine their family uniquely.
Source: canonical ordered source recursion
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: at zero use ordinaryDescentZeroRaw. At a successor use ordinaryDescentStepRaw
on the preceding comparison. Unfold affineTraceRight and affineTraceProjection at their
outermost successor, and affineLinearBaseCoefficient at its outer successor. Their
endpoints are the displayed ones, by the canonical pullback and tensor associators.
Transport the raw map along these endpoint equalities. Recursion constructs the family.
Induction and HEq transitivity show any two families have equal hom components; Iso.ext
and funext give equality of the families. No scalar automorphism is inserted. -/
theorem ordinarySourceDescent_existsUnique (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) :
    ∃! e : (d : ℕ) → (Etale.affineTraceRight A N hA Y d).obj K ≅
      (Etale.ordinaryFinitePullback A (affineTraceProjection Y d)).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
          (Etale.affineLinearBaseCoefficient A N hA Y d)),
      HEq (e 0).hom (ordinaryDescentZeroRaw A Y K).hom ∧
        ∀ d : ℕ, HEq (e (d + 1)).hom
          (ordinaryDescentStepRaw A N hA t Y hY K d (e d)).hom := by
  exact iso_rec_unique _ _ (ordinaryDescentZeroRaw A Y K)
    (fun d ed ↦ ordinaryDescentStepRaw A N hA t Y hY K d ed)

/-- The uniquely specified canonical ordinary source descent. Its defining recursion
fixes every hom component by explicit canonical maps.
Source: ordered affine source identification
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinarySourceDescent (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) : (d : ℕ) →
    (Etale.affineTraceRight A N hA Y d).obj K ≅
      (Etale.ordinaryFinitePullback A (affineTraceProjection Y d)).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
          (Etale.affineLinearBaseCoefficient A N hA Y d)) :=
  (ordinarySourceDescent_existsUnique A N hA t Y hY K).exists.choose

/-- The ordered ordinary right source is the literal pullback/tensor coefficient source.
Source: normalized finite Tate pullback and canonical tensor associators
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinarySourceIsoFixed (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) (d : ℕ) :
    (Etale.affineTraceRight A N hA Y d).obj K ≅
      ((Etale.ordinaryFiniteTensor A (affineTraceTower Y d)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A)
          (affineTraceProjection Y d)).mapDerivedCategory.obj K)).obj
          (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower Y d) d) :=
  ordinarySourceDescent A N hA t Y hY K d ≪≫
    Etale.ordinaryFiniteTensorPullback A (affineTraceProjection Y d) K
      (Etale.affineLinearBaseCoefficient A N hA Y d) ≪≫
    Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d) (Iso.refl _)
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA t
        (affineTraceProjection Y d) hY d) ≪≫
    Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d)
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (affineTraceProjection Y d)).app K) (Iso.refl _)

/-- The source comparison at the specified finite coefficient ring.
Source: canonical ordinary source coordinates
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinarySourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y) (d : ℕ) :=
  ordinarySourceIsoFixed (AffineLinePurity.Ring P) (exponent P) (annihilates P) (transport P)
    Y (exponentUnit P Y aY) K d

/-- The canonical proper/open tower comparison at any bounded-below ordinary input.
Source: lem-amb-unbounded-compact-support-comparisons
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryCompactComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (M : DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Etale.affineTraceLeft A Y d).obj M.obj ≅
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection Y d)).obj M.obj :=
  ((Etale.affineTracePlusCompatibility A Y d).app M).symm ≪≫
    DerivedCategory.Plus.ι.mapIso ((Etale.affineTraceCompactSupportComparison A Y d).app M) ≪≫
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).app M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The ordered right adjoint preserves the stated finite-Tor boundedness domain.
Source: finite Tate tensor and pullback preservation
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: ordinarySourceIso identifies the ordered source with pullback of K tensored with
an ordered product of shifted locally free Tate lines. Pullback preserves bounded finite
Tor amplitude and constructibility. Tensor with each line translates the bounds by two.
In particular the result is bounded below, including d=0, K=0 and the empty base. -/
theorem ordinarySource_plus (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    DerivedCategory.TStructure.t.plus
      ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P) (annihilates P) Y d).obj K)
        := by
  have h0 : DerivedCategory.TStructure.t.plus K := hK.1.1.1
  induction d with
  | zero => exact h0
  | succ d ih =>
    let T := affineTraceTower Y d
    let J := (Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
      (annihilates P) Y d).obj K
    have hT := affineTraceInvertible (exponent P) Y (exponentUnit P Y aY) d
    have hX := affineTraceProjectiveInvertible (exponent P) T hT
    have hp := pullback_plus (AffineLinePurity.Ring P) (ProjectiveLine T ↘ T) J ih
    have ht := tensorLine_plus (AffineLinePurity.Ring P) (exponent P)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (ProjectiveLine T) hX _ hp
    exact pullback_plus (AffineLinePurity.Ring P) (ProjectiveLine.affineChart T) _ ht

/-- The ordered ordinary counit, written using the standing compact-support functor.
Source: ordered adjunction and normalized proper/open compositor
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ordinaryCounit (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :=
  (ordinaryCompactComparison (AffineLinePurity.Ring P) Y d
    ⟨_, ordinarySource_plus P Y aY K hK d⟩).inv ≫
      (orderedAdjunction P Y aY d).counit.app K

/-- The coefficient-counit square, before specializing the coefficient ring.
Source: the displayed counit formula after precomposition by the actual projection
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def OrdinaryCounitEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (J : Etale.DerivedCategoryModule A X)
    (e : J ≅ ((Etale.ordinaryFiniteTensor A X).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj W)
    (z : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J ⟶ K)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      Etale.ordinaryFiniteUnit A Y) : Prop :=
  Etale.compactSupportProjectionMap A f W K ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map e.inv ≫ z =
    (Etale.ordinaryFiniteTensorTrace A Y t).app K

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
