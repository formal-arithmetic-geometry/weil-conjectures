/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Submission.WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
public import Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Submission.WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
public import Submission.WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Submission.WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Submission.WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
public import Submission.WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
public import Submission.WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
public import Submission.WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import Submission.WeilConjectures.Compactification.NagataCompactification
public import Submission.WeilConjectures.Compactification.Defs
public import Submission.WeilConjectures.SixFunctors.OpenClosed.Complex
public import Submission.WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
public import Submission.WeilConjectures.Mathlib.RingTheory.Henselian
public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import Submission.WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import Submission.WeilConjectures.RingTheory.StrictHenselizationTriples
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselization
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import Submission.WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
public import Submission.WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import Submission.WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Submission.WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import Submission.WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Submission.WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
import Submission.WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
public import Submission.WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.SixFunctors.OpenClosed.Exact
public import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
public import Submission.WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
public import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenAdjunctionNormalization
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPasting
import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.Algebra.Homology.Localization
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.CategoryTheory.DerivedExactMate
import Submission.WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import Mathlib.CategoryTheory.Generator.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Unbounded proper/open interchange and its canonical normalizations

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B (case (b)), 0F7C, 0F7D
and 0F7F (blueprint: lem-amb-unbounded-proper-open-interchange).

The sheaf isomorphism is specified by equality of its two maps into the common direct
image. This is precisely equality of the proper-support subsheaves, and fixes the map.
The derived isomorphism is specified on every K-injective representative and every
K-injective resolution of its open extension. All composition equations include the
canonical composition isomorphisms. No boundedness of the input is imposed.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private structure NormalizedDerivedComparison
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P) where
  comparison : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
        K.mapDerivedCategory ⋙ P.rightDerivedFunctor
  unit_normalization : (∀ X : HomotopyCategory C₀ (.up ℤ),
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app X) ≫
          comparison.hom.app (DerivedCategory.Qh.obj X) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app X) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj X) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app X))
  representative_normalization : ∀ (J : CochainComplex C₀ ℤ)
        [J.IsKInjective]
        (I : CochainComplex C₁ ℤ)
        [I.IsKInjective]
        (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        E.mapDerivedCategory.map
            ((R).rightDerivedFunctorObjQIso J).hom ≫
          (E).mapDerivedCategoryFactors.hom.app
            ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            ((P.mapHomologicalComplex (.up ℤ)).map ρ) =
        comparison.hom.app (DerivedCategory.Q.obj J) ≫
          P.rightDerivedFunctor.map
            ((K).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          ((P).rightDerivedFunctorObjQIso I).hom

end AlgebraicGeometry.Etale
