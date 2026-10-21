# PbcAutomorphismTransport: local proof commands and declaration ordering

## Reason

Stage-3 preflight conservatively classifies added top-level `attribute` and scoped
`set_option` commands, together with declaration ordering, as an interface change.
Record those commands explicitly. They control elaboration of proofs in this module;
none changes a public declaration signature, data definition body or public import.
The theorem `pbcIsoAmbientPullback_preserves` is moved before
`pbcIsoCompletedComparison_isIso` so that the latter can apply the existing theorem.
Its original statement, source/proof docstring and `sorry` body are preserved.

## Old

The existing outer settings and scope were:

```lean
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
```

There were no local reducibility attributes or scoped backward-definitional-equality
settings. `pbcIsoAmbientPullback_preserves` followed the completed comparison and its
identification definition. The two existing `include hf in` wrappers belonged to
`pbcIsoCoefficientMap_isIso` and `pbcIsoCompletedComparison_isIso`.

## New

The old outer settings, variables and namespace remain verbatim. Proved private
category-theoretic helpers precede the namespace. Before the public proofs, add:

```lean
attribute [local irreducible] completedCoefficientMap proEtaleRingModulePullback
  proEtaleIsoPostcompose pbcScalarExtension pbcIntegralScalarExtension
```

Before the integral scalar comparison, restore the two scalar functors locally:

```lean
attribute [local semireducible] pbcScalarExtension pbcIntegralScalarExtension
```

These attributes prevent expensive expansion of chosen module/scalar functors in
categorical arguments, while allowing the later integral full-subcategory proof to
reduce the scalar functors to their recorded ambient functors. They are local to the
namespace and are not exported. Certain private helpers and the ambient scalar theorem
use the following declaration-scoped settings:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

Some private helpers use only the first line. The rationalization theorem has:

```lean
set_option linter.unusedSectionVars false in
```

This preserves its original section-instance binders while proving the original
statement by functor extensionality. Neither setting changes a declaration's meaning.
The original two `include hf in` wrappers remain attached to the same theorems.
Only the preservation theorem's position changes; no definition or public signature
changes, and no downstream module requires adaptation. The complete file compiled
cleanly in 39.4 seconds through the prescribed remote compiler.

## Users

`tools/downstream.py Sheaf.Paper.PbcAutomorphismTransport --uses` was run for the
transport functors and comparison definitions. Its textual declaration hits outside
the item are `Sheaf.Paper.PbcWeilCategory` and `Sheaf.Paper.WeilTensorProduct`.
The table includes the item and all 128 transitive downstream modules reported by
`tools/downstream.py`; holders are read from module/node claims at packet preparation.
Every existing signature, public import and data definition remains unchanged, and
all added attributes/settings are local, so the effect for every downstream user is
none. No user file is included or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.PbcAutomorphismTransport` | M5 | Twelve proofs filled; local proof commands; existing theorem reordered. |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | unclaimed | None; no adaptation. |
| `Sheaf.Algebra.Homology.RingedSiteTorFlatModel` | unclaimed | None; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectLowerModel` | unclaimed | None; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract` | unclaimed | None; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectTorWindow` | unclaimed | None; no adaptation. |
| `Sheaf.Algebra.Homology.SitePerfectUpperModel` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeometricSpecializationCategory` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.MultipointedCurveModification` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.SemistableMultipointedPair` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.StableModificationStabilityLocus` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlySemistableCurve` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction` | unclaimed | None; no adaptation. |
| `Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.SiteTorIntervalRestriction` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentConservativeReflection` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentObjectApproximation` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.CoherentToposRepair` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent` | unclaimed | None; no adaptation. |
| `Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.AlterationBlowupFinite` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.AlterationFiniteRefinement` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.CoefficientChangeDualizing` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.CoherentSetCriterion` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.CtfHomCoefficientComparison` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.GeneralNearbySliceTest` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.HomUniversalCoefficients` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | Q4, Q95 | None; no adaptation. |
| `Sheaf.Paper.LocallyConstantPerfectComplex` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.ModificationClosedImageLifting` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.ModificationsZariskiRefinement` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.NearbyClosedImage` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.NearbyGeometricSlice` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.NearbyProperHyperdescent` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.NearbySpreadOut` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrgogozoInductionData` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedClosedBaseRestriction` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleCoherent` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSetSheaf` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSheaf` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSheafVanishing` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSubquotients` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedHypercoverDescentDatum` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedMaximalPointFiniteness` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedNearbyCycles` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedProductPointsConservative` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedProperFibreExchange` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.OrientedSourceLocalization` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.PbcWeilCategory` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.PlurinodalProperHypercover` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.PsiConstructibilityDescent` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.StratifiedOrientedCover` | unclaimed | None; no adaptation. |
| `Sheaf.Paper.WeilTensorProduct` | Q20 | None; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable` | unclaimed | None; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.NodalEtaleChart` | unclaimed | None; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel` | unclaimed | None; no adaptation. |
| `Sheaf.SixFunctors.TraceFormula.NodalLogRegularity` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ClosedImageGenericAlteration` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ContractedComponentGenericData` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ContractedComponentNoExtraGeneric` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.CurveP1TreeLocalCriterion` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ExceptionalComponentSpecialization` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.FinitarySiteCoherentGenerators` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.FiniteEtaModificationGluing` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.FiniteFibreValuationDomination` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.LocalMarkingLength` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.MarkedCurveFiniteTypeModel` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.NodalContractionNormalizationBranches` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointCohomology` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointNormalizedStratum` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ProjectiveLineTree` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ProperBaseChangeCoherentConservative` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ReducedFibreModification` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.SemistableMarkedPoint` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.SemistableModificationFibreContractions` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.SemistableNormalTargetFactorization` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.SingleValuationSemistableExtraction` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.StableCurveDiagramNoetherianModel` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.StableModificationConstructibility` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.StableModificationSpreading` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.StableModificationStabilityFieldDescent` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.TemkinStableModification` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationCurveProjectivePreparation` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationExceptionalLocalCriterion` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationHorizontalCurveModels` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationMarkingSemistableSeparation` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationModificationProperCompletion` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationNormalizedGraphModel` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationReducedFibreNormalization` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationSemistableDominatesStable` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationStrictSemistableCofinality` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization` | unclaimed | None; no adaptation. |
| `Sheaf.TraceFormula.ValuationSymmetricNodalBlowup` | unclaimed | None; no adaptation. |

## Status

landed 20261021T111341-L-77970 2026-10-21 (merge of deliver/M5/Sheaf.Paper.PbcAutomorphismTransport)
