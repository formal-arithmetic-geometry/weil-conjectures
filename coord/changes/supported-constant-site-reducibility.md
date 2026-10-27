# AlgebraicGeometry.SupportedConstantNormalization.topology and siteCategory

## Reason

Expose the Boolean site and topology aliases to Lean's implicit transparency.
The old definitions require expensive conversions between `Modules A true X`
and the existing pro-etale sheaf category in adjunction calculations. The new
bodies are identical, with only the reducibility hint changed. Neither the
selected site nor its category, topology, coefficient universe, or morphisms
changes. All target statements and every other public construction are preserved.

A whole-module check with the original reducibility hints fails at the actual
inverse-image finite-limit and finite-colimit instances (`failed to synthesize
PreservesFiniteLimits (pull A false h)`, and the corresponding pro-etale and
colimit instances), and the etale square calculation reports an application
type mismatch between the native sheaf category and `Modules A false X` under
implicit transparency. The identical-body aliases expose those categories to
instance synthesis; no new exactness hypothesis is introduced.

## Old

```lean
instance siteCategory (pro : Bool) (X : Scheme.{u}) : Category.{u} (Site pro X) :=
  match pro with
  | false => inferInstance
  | true => inferInstance

def topology (pro : Bool) (X : Scheme.{u}) : GrothendieckTopology (Site pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => Scheme.ProEt.topology X
```

## New

```lean
@[reducible] instance siteCategory (pro : Bool) (X : Scheme.{u}) : Category.{u} (Site pro X) :=
  match pro with
  | false => inferInstance
  | true => inferInstance

abbrev topology (pro : Bool) (X : Scheme.{u}) : GrothendieckTopology (Site pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => Scheme.ProEt.topology X
```

## Users

`tools/downstream.py --uses` finds the following explicit users. The full
import graph also contains transitive consumers, whose public signatures are
unchanged because these definitions remain definitionally identical. The
siteCategory name is used explicitly only in the item itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | T3 | Identical category and topology; no adaptation required. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CoordinateBoundaryGeometricPullback | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.FramedProPredicate | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SectionCompactSourceExchange | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SupportedClassEvaluationComparison | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Identical category and topology; no adaptation required. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | unclaimed | Identical category and topology; no adaptation required. |

The mathematical meaning of targets that reach these definitions is unchanged:
the same match expressions select the same etale/pro-etale sites and topologies.
This record explicitly flags the definition-hint change for independent review.

## Status

landed 20261024T191216-L-272422 2026-10-24 (merge of deliver/T3/Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization)
