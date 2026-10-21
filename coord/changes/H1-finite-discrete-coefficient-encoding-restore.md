# AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientEquivalence

## Reason

Restore the implementation quarantined by the cluster restore recorded in
coord/rework.tsv (2026-10-20). The live source is absent; its archive is preserved at
quarantine/Sheaf/Paper/FiniteDiscreteCoefficientEncoding.lean. The archived module
compiles unchanged against the current server dependencies in 4.3 seconds.
This repairs the missing definition and its underlying-sheaf comparison by restoring
the actual constructive module, with its original Lean attachment and dependencies.
It is not a withdrawal or an empty replacement.

## Old

The live module lean/Sheaf/Paper/FiniteDiscreteCoefficientEncoding.lean is absent.
The quarantined implementation is the exact text shown under New below.

## New

Restore the following archived module verbatim; all signatures, public imports,
attributes, construction bodies, and the forgetful isomorphism agree with the archive.

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import Sheaf.Paper.FiniteDiscreteRealizationFunctor
public import Sheaf.Paper.ConstantInternalModuleSheafEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Sheaf.Paper.FiniteDiscreteSchemeRing

/-! # A common sectionwise finite-coefficient encoding

The same functor on internal modules in abelian groups is used on every site.
The coefficient-ring identification is pulled back from one fixed profinite point.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme CategoryTheory.ConstantInternalModuleSheafEncoding

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

/-- Encode coefficient sheaves using a single sectionwise encoding and point ring.
Source: Bhatt--Scholze, Proposition 5.3.2; the constructive constant-ring encoding
(blueprint: def-weil-pbc-common-finite-discrete-encoding).

Construction. Invert the sectionwise sheafEncoding for the fixed G, then invert
restriction of scalars along the ring isomorphism pulled back from eR at the point.
Both functors and their equivalence structures are given by proved constructions. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientEquivalence (T : Scheme.{u}) :
    FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  exact (sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG).asEquivalence.symm.trans
    (Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B T eR).hom).symm

/-- This coefficient encoding preserves the underlying abelian sheaf. -/
noncomputable def finiteDiscreteCoefficientEquivalenceForgetIso (T : Scheme.{u}) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).functor ⋙ Mod.forget _ ≅
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  let H := sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG
  let U := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  unfold finiteDiscreteCoefficientEquivalence
  change H.inv ⋙ Mod.forget _ ≅ U
  exact Functor.isoWhiskerLeft H.inv
      (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight H.asEquivalence.counitIso U ≪≫ Functor.leftUnitor U

end AlgebraicGeometry.ProEtale.CondensedRing
```

## Users

The live downstream.py command reports this module unknown because it is quarantined.
Instead, an import-graph scan of both lean/ and quarantine/ (live sources taking
precedence) finds 10 direct importers and 153 transitive consumers. The table includes
them all. No consumer is edited. Their statements and constructions regain the exact
archived definition, with no change of meaning or forced adaptation. Holder queries
are unnecessary for unchanged consumers; no work is taken from another group.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.AdmissibleVerdierExchange | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.CurveIntermediateExtension | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeCompactComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeCompactScalar | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteFreeScalarProjection | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteTorStability | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.GlobalVerdierDuality | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.IntegralDirectImageTower | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.IntegralExchangeReduction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.MateOpenRestriction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.NonrationalCompositionSeed | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ProjectionFiniteReduction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ProperProductCounitTranspose | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalExceptionalRestriction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalHomScalarTranspose | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalRestrictionGlue | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalTensorSymmetry | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.RestrictionLocal | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.ScalarExchangeConstituents | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.SfBidualityClass | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.SitePerfectRationalBidual | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.TateTwistSupportCondition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.TensorAdjunctionExchange | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Paper.VerdierExchange | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not queried; not adapted | Direct consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteDualizing | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteExceptional | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralDualizing | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.IntegralVerdier | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.RationalOperations | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctors.RationalVerdier | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Targets.AffineSpaceRationalLine | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Targets.PoincareUncurry | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.Targets.SmoothPurityQbar | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.PoincareDuality.Poincare | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.PoincareDuality.Verdier | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.SmoothPurity.Defs | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.TraceFormula.Basic | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.Main | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried; not adapted | Transitive consumer in lean; exact archived interface restored. |
| WeilConjectures.TraceFormula.Statement | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; not adapted | Transitive consumer in quarantine; exact archived interface restored. |

## Status

landed 20261021T021012-L-2690565 2026-10-21 (merge of deliver/H1/Sheaf.Paper.FiniteDiscreteCoefficientEncoding)
