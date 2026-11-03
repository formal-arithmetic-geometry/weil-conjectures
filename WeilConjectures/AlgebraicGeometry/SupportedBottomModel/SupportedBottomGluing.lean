/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles

import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
import Mathlib.Order.WithBotTop
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.CategoryTheory.CartanEilenbergMappedTotal
import WeilConjectures.CategoryTheory.Derived.DerivedInjectiveResolutionNaturality
import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Homology.HomologicalBicomplex
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.CategoryTheory.GrothendieckResolutionUnitComparison
import WeilConjectures.CategoryTheory.SpectralObjectBottomFiltration
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.GrothendieckEdgeCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.RightDerivedInjectiveSequence
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Purity.PurityComparisonUnitInjectiveModel
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology

/-!
# Supported cohomology in the lowest local degree

Source: Stacks Project, Tags 015N, 09XP, 09XQ and 099V
(blueprint: lem-pur-supported-bottom-gluing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u vC uC vD uD
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

open CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace SupportedBottomModel

/-- The displayed etale edge on the actual supported group on U, with the coefficient
identified with A_U(a) by the finite-twist pullback theorem.
Source: Stacks 015N and 09XP (blueprint: lem-pur-supported-bottom-gluing). -/
def etaleEdgeAt {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) (U : X.Etale) :
    Etale.supportCohomologyValue (pullback.snd i U.hom) d
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} U.hom inferInstance).obj
        ((bottomForgetEt (bottomCoefficient P) X).obj (bottomEtaleTwist P X r hA a))) ≅
      (M.etaleComplex.homology d).obj.obj (op U) :=
  letI := M.additiveEt
  (M.localEt U).groupIso d ≪≫ e.edge.app (op U)

/-- The displayed etale edge with literally the prescribed A_U(a) coefficient sheaf.
Source: Stacks 015N, 09XP and 03PK (blueprint: lem-pur-supported-bottom-gluing). -/
def etaleTateEdgeAt {P : PurityFiniteSetting.{u}} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of P.field.k))] {Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] {r : ℕ}
    {hA : ((P.coefficients.l ^ (r + 1) : ℕ) : bottomCoefficient P) = 0} {a : ℤ}
    {Theta : SignedFiniteTateComparison P} (M : SupportedBottomModel P X i r hA a Theta)
    {d : ℕ} (e : SupportedBottomEdge M.etaleComplex d) (U : X.Etale) :
    Etale.supportCohomologyValue (pullback.snd i U.hom) d
      ((bottomForgetEt (bottomCoefficient P) U.left).obj
        (bottomEtaleTwist P U.left r hA a)) ≅
      (M.etaleComplex.homology d).obj.obj (op U) :=
  ((Etale.supportSections (pullback.snd i U.hom)).rightDerived d).mapIso
    (bottomLocalCoefficientEt Theta U r hA a).symm ≪≫ M.etaleEdgeAt e U

end SupportedBottomModel

end AlgebraicGeometry
