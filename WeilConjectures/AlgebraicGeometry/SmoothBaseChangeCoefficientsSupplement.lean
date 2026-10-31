/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SbcExchangeCompatibility
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability
import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
import WeilConjectures.AlgebraicGeometry.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.SixFunctors.ReductionToFinite
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantEtaleSections
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Presheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartCounit
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedEssentialImage
import WeilConjectures.AlgebraicGeometry.CoefficientOriginOpenCover
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.AlgebraicGeometry.CoefficientOriginAffineOpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientOriginClosedDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealizationSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalModuleOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientOriginLocalizationKernel
import WeilConjectures.AlgebraicGeometry.CoefficientFixedLocalizationKernelComparison
import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.CoefficientOpenClosedKernel
import WeilConjectures.AlgebraicGeometry.CoefficientOpenExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonInjectiveAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineSections
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineCech
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechPresentation
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechSystem
import WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction
import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
import WeilConjectures.CategoryTheory.Sites.CechComplex
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.CategoryTheory.Pro.Generating
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.CategoryTheory.Sites.CechComplexRelativeLimit
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.ModuleCechCriterion
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonModuleEquivalence
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonModuleCriteria
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalSingle
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstructibilityTest
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence

/-! # Smooth base change for all admissible coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sbc-coefficients/_section.md, node order 2863
(blueprint: sk-thm-sbc-coefficients).
The theorem retains the arbitrary-field domain of the blueprint unit. It uses the
published canonical exchange and scalar comparison maps. Its proof requires extending
the available finite-base-CD scalar interfaces to this domain; see the worker report.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- Smooth base change in the ordinary uncompleted constructible categories, its
identity and two pasting equations, its scalar-comparison rectangle, and Dctf = Dbc
for the integral and rational stages.

Source: latest blueprint, sec-six-functors-basics/sk-thm-sbc-coefficients,
_section.md and sk-thm-sbc-coefficients.proof.md, all clauses
(blueprint: sk-thm-sbc-coefficients).

Proof: First finite type over a field implies the Noetherian and qcqs hypotheses by
lem-weil-pbc-finite-type-over-noetherian, locally-noetherian-quasi-separated and
qcqs-morphism-permanence. For finite rings, sk-def-sfb-constructible makes K bounded
constructible; sk-thm-pe-constructible-comparison identifies it with a classical etale
complex. A power of ell kills its coefficients and is invertible on the base, so
sk-thm-sbc-derived makes exchange invertible. Next sk-thm-sf-ctf-stability puts both
exchange functors on Dctf. The module-derived-functor-compositor-shifts and
kflat-derived-adjunction-transport-shifts lemmas make them exact and make exchange
commute with shifts. Apply scalar-six and sbc-exchange-compatibility to obtain scalar
comparison isomorphisms and their rectangle; sk-prop-reduction-to-finite then extends
the finite-ring assertion to integral, rational and algebraically closed coefficients.
The published scalar/stability interfaces currently require finite base CD, so this
step needs an independent arbitrary-field extension; no such hypothesis is silently
added here. Identity and both pasting laws are the equations of
sk-lem-sbc-exchange-compatibility for the same canonical exchange, so remain valid when
its components are invertible. Finally lem-integral-ctf-equals-bc identifies the object
predicates in the nonfinite cases, with no assertion at nonregular finite rings. -/
theorem smoothBaseChangeAllAdmissibleCoefficients (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] :
    (∀ (Λ : ScalarSixRing.{u}) (_hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
        {X' X Y' Y : Over (Spec (.of k))}
        [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
        (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
        (sq : ChosenCartesianSquare u.left f'.left f.left g.left) [Smooth g.left]
        (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      IsIso ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq.w).app K.obj)) ∧
    (∀ (Λ : ScalarSixRing.{u}) (_hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X),
      (∀ {X Y : Over (Spec (.of k))}
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
          (sq : ChosenCartesianSquare (𝟙 X.left) f.left f.left (𝟙 Y.left))
          (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
        (RootCoordinateFace.exchange Λ.X (𝟙 X.left) f.left f.left (𝟙 Y.left) sq.w).app K.obj =
          (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X Y.left) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app
            ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
          (RootCoordinateFace.lower Λ.X f.left).map
            ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ.X X.left) ≪≫
              Functor.mapDerivedCategoryIdIso _).inv.app K.obj)) ∧
      (∀ {X'' X' X Y'' Y' Y : Over (Spec (.of k))}
        [LocallyOfFiniteType X''.hom] [QuasiCompact X''.hom] [IsSeparated X''.hom]
        [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y''.hom] [QuasiCompact Y''.hom] [IsSeparated Y''.hom]
        [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
          {u : X' ⟶ X} {u' : X'' ⟶ X'}
          {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
          {g : Y' ⟶ Y} {h : Y'' ⟶ Y'}
          (sq₁ : ChosenCartesianSquare u.left f'.left f.left g.left)
          (sq₂ : ChosenCartesianSquare u'.left f''.left f'.left h.left)
          (outer : ChosenCartesianSquare (u'.left ≫ u.left) f''.left f.left (h.left ≫ g.left))
          [Smooth g.left] [Smooth h.left]
          (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
        (RootCoordinateFace.exchange Λ.X (u'.left ≫ u.left) f''.left f.left
          (h.left ≫ g.left) outer.w).app
          K.obj =
          (RootCoordinateFace.upperComp Λ.X h.left g.left).hom.app
            ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
          (RootCoordinateFace.upper Λ.X h.left).map
            ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq₁.w).app K.obj) ≫
          (RootCoordinateFace.exchange Λ.X u'.left f''.left f'.left h.left sq₂.w).app
            ((RootCoordinateFace.upper Λ.X u.left).obj K.obj) ≫
          (RootCoordinateFace.lower Λ.X f''.left).map
            ((RootCoordinateFace.upperComp Λ.X u'.left u.left).inv.app K.obj)) ∧
      (∀ {X' X Y' Y Z' Z : Over (Spec (.of k))}
        [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
        [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
        [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
          {u : X' ⟶ X} {f' : X' ⟶ Y'}
          {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
          (sq₁ : ChosenCartesianSquare u.left f'.left f.left v.left)
          (sq₂ : ChosenCartesianSquare v.left e'.left e.left g.left)
          (outer : ChosenCartesianSquare u.left (f'.left ≫ e'.left) (f.left ≫ e.left) g.left)
          [Smooth g.left]
          (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
        (RootCoordinateFace.exchange Λ.X u.left (f'.left ≫ e'.left) (f.left ≫ e.left)
          g.left outer.w).app
          K.obj =
          (RootCoordinateFace.upper Λ.X g.left).map
              ((RootCoordinateFace.lowerComp Λ.X f.left e.left).hom.app K.obj) ≫
          (RootCoordinateFace.exchange Λ.X v.left e'.left e.left g.left sq₂.w).app
            ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
          (RootCoordinateFace.lower Λ.X e'.left).map
            ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left v.left sq₁.w).app K.obj) ≫
          (RootCoordinateFace.lowerComp Λ.X f'.left e'.left).inv.app
            ((RootCoordinateFace.upper Λ.X u.left).obj K.obj))) ∧
    (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
        {X' X Y' Y : Over (Spec (.of k))}
        [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
        (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
        (sq : ChosenCartesianSquare u.left f'.left f.left g.left) [Smooth g.left]
        (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      (scalarSixPullHom a g.left).app ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
          (scalarSixPull Λ' g.left).map ((scalarDirectImageMate a f.left).app K.obj) ≫
          (RootCoordinateFace.exchange Λ'.X u.left f'.left f.left g.left sq.w).app
            ((scalarSixChange a X.left).obj K.obj) =
        (scalarSixChange a Y'.left).map
            ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq.w).app K.obj) ≫
          (scalarDirectImageMate a f'.left).app ((scalarSixPull Λ u.left).obj K.obj) ≫
          (RootCoordinateFace.lower Λ'.X f'.left).map
            ((scalarSixPullHom a u.left).app K.obj)) ∧
    (∀ (X : Over (Spec (.of k)))
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        (Λ : ScalarSixRing.{u})
        (hΛ :
          Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
          Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
          (∃ E : PadicAlgCl.FiniteIntermediateField ell,
            Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
            Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
          Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))),
      (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ.X X.left) := by
  sorry

end AlgebraicGeometry.Scheme
