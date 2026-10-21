# AlgebraicGeometry.StandardSingleFlatCounitPresentation imports

## Reason

Restore the assigned quarantined definition module from the exact archive in its
`coord/rework.tsv` row. The original archive fails against the current published
library: at line 45 Lean cannot synthesize `(Scheme.Modules.tensorPullback g).Additive`,
and at line 52 `SingleComplexBaseChange.counit` is unknown. The old Sheaf
stalk-condition module is now an empty withdrawn module. The adopted upstream
module supplies both declarations, as already recorded by the dependency node
`def-pc-single-complex-base-change-stalk-condition` and the landed B2 migration
`coord/changes/B2-derived-pullback-source-construction.md`.

Redirect that public import to its actual provider. Both existing definitions,
including their complete bodies, binders, universes, docstrings and visibility,
remain verbatim from the quarantine archive. No mathematical predicate, target,
source-library declaration or DAG edge is changed. The archive remains intact.
This is a zero-hole restoration and import repair, not a theorem proof.

## Old

The source path is absent; the preserved archive is
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitPresentation.lean`.
Its imports are:

```lean
public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
```

## New

Restore `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitPresentation.lean`
with exactly these imports and the archived declaration text:

```lean
public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
--uses StandardSingleFlatCounitPresentation StandardSingleFlatCounitOnOpen
--allow-missing` finds zero live consumers because this root and its consumers are
quarantined. A reverse import-graph scan across both `lean/` and `quarantine/`, with
live files overriding archives, finds 13 direct and 76 transitive archived consumers,
listed below. Their text is not changed by this packet. Restoration retains the
original existential presentation, its boundedness and flatness conditions, both
isomorphisms, the canonical counit equation, and the open-wise universal property.
It changes no assumptions or conclusions of these consumers. No consumer adaptation
is required for the import repair. The two original localization data and pair
modules and the original affine presentation consumer are compiled unchanged
against this restored root in scratch checks. A `#print axioms` probe reports only
`propext`, `Classical.choice`, and `Quot.sound` for both definitions.
Other quarantined modules remain separate rework items; this packet does not claim
to restore their closures. No current target imports this missing source path.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationData | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPair | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnion | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionCore | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionPresentation | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.UnionBoundedAboveModel | unclaimed | Archived direct consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Archived transitive consumer; no text or statement changed. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Archived transitive consumer; no text or statement changed. |

Both definition nodes keep their existing Lean attachments, statements and
empty proof plans. The imported counit provider already matches the current
attachment of their dependency node, so no DAG edit is needed.

## Status

landed 20261021T003459-L-1642195 2026-10-21 (merge of deliver/B3/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation)
