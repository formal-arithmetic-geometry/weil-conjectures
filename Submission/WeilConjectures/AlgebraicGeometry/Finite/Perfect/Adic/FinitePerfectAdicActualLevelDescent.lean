/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualLevels
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleStalkData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Homology.Homotopy
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import Submission.WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Submission.WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.SixFunctors.BaseChange.Square
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Submission.WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
import Submission.WeilConjectures.ConstructibleSheaf.InternalHom
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Submission.WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Submission.WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
import Submission.WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import Submission.WeilConjectures.SixFunctors.ProEtale.ScalarExtension
import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsSquare
import Submission.WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransitionUnit
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransitionUnique
import Submission.WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Submission.WeilConjectures.CategoryTheory.Adjunction.MateVCompIsIso
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStrictRealizationComparison
import Submission.WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteComparison
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation
import Submission.WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import Submission.WeilConjectures.AlgebraicGeometry.Etale.EtaleSourceNormalizationUniversal
import Mathlib.CategoryTheory.Adjunction.Comma
import Submission.WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Descent of the actual quotient tower with its comparison retained

Source: Stacks Project, Tags 09AL, 09B1, 09C6 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- A specified etale diagram descends the actual quotient tower only when its
realization and its consecutive arrows compare with that tower. Stalkwise agreement
with the algebraic model alone does not express this requirement.
Source: Stacks Tags 09AL, 09C6 and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-descent). -/
structure FinitePerfectAdicActualLevelDescent
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (L : FinitePerfectAdicActualLevelData X d M V T) where
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (L.K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (L.dK n)) ≫
      (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (L.K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op

end AlgebraicGeometry.Scheme
