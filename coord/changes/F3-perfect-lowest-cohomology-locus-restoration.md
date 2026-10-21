# AlgebraicGeometry.Scheme.exists_perfectLowestCohomologyLocus

## Reason

Restore the quarantined module assigned by coord/rework.tsv. The archived module
has a complete proof and zero holes. Its public import of the withdrawn duplicate
Sheaf.AlgebraicGeometry.DerivedPullback no longer exposes the definitions in its
statement. Compiling the unchanged archive reports unknown identifiers
`derivedPullback` (lines 82, 86, 95) and `Modules.tensorPullback` (line 89), with
compiler suggestions to publicly import the adopted upstream modules.
The existing B2-derived-pullback-source-construction migration already established
these upstream definitions as the project's shared API.

## Old

Archived imports, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullback
```

The complete theorem signature and proof body are preserved verbatim. No definition,
statement, target signature, or source-library module is edited. The node attachment
and all three recorded proof dependencies remain intact. The restored module compiles
through lcompile.py against the current upstream API without errors or warnings.

## Users

`tools/downstream.py` reports the item as unknown because quarantined modules are
absent from the live Lean graph. An equivalent reverse-import traversal over both
lean/ and quarantine/ (preferring live sources) finds 24 transitive consumers.
The two direct consumers, PicardUniversalSingleRankLocus and
PicardUniversalSingleRankLocusFinitePresentation, both apply the unchanged theorem
with the same arguments and result projections. They need no adaptation for this
repair; their separate quarantine repairs remain separate items. No target meaning
changes beyond the already reviewed shared upstream migration.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.GeneralTheoremOfCube` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus` | F3 | Restored with upstream public imports; theorem unchanged. |
| `Sheaf.AlgebraicGeometry.PicardCupProductBaseChange` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterion` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardH1IntersectionSection` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalDescent` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardH1MultipleLocus` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosed` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardProductOpen` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardProductOpenData` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardPullbackEvaluation` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus` | unclaimed | Interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation` | unclaimed | Interface unchanged; no adaptation required. |

## Status

landed 20261021T014704-L-2444806 2026-10-21 (merge of deliver/F3/Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus)
