# CategoryTheory.site_point_reconstruction_sets: proof-scope commands

## Reason

The stage-3 static gate classifies newly added `open` and `variable` commands as
an interface change. This record documents them. All four existing public
non-theorem declarations have identical source bodies, and the existing theorem
has an identical signature. Every additional helper in the item module is
private. No existing instance, attribute, notation or public import changes.
The new namespace confines the product-proof variables and names; its `open`
commands only affect elaboration in this source file. Consumers see the same
existing public declarations and types. No target definition or statement changes.

## Old

The existing scope command, verbatim:

```lean
open Limits Opposite
```

## New

The existing command remains verbatim. The product proof adds this scoped block
(with proved private declarations between its last two commands):

```lean
namespace BinaryProductProof

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

end BinaryProductProof
```

The new public equalizer statement is recorded in its own new DAG node; it is a
strict part of the existing source proof. It does not change an existing signature.

## Users

`tools/downstream.py Sheaf.Paper.SitePointReconstructionSets --uses
site_point_reconstruction_sets` finds only `FpStalkRealization` outside the item
as a direct user of that theorem (five calls). The definitions also occur in
`SitePointFibre`. The three direct importing modules are `SitePointFibre`,
`FpStalkRealization`, and `OrientedPointNormalizedStratum`. Their source uses the
unchanged public API; no source adaptation is necessary. The following table lists
all 34 transitive importers reported by `downstream.py`, with their current claims.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion` | F2 | Unchanged public API; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.CategoryTheory.SitePointFibre` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.CategoryTheory.Sites.FpStalkRealization` | H4 | Unchanged public API; no adaptation. |
| `Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.CategoryTheory.Sites.OrientedProductSliceLocalization` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.CoherentSetCriterion` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.GoodOrientedNearbyKunneth` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.NearbyClosedImage` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.NearbyCyclesDimensionBound` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.NearbyFiniteBaseDescent` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.NearbyGeometricSlice` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.NearbySpecializationSlice` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedAffineNeighbourhoodLimit` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedClosedBaseExtension` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleCoherent` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedConstructibleSubquotients` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedMaximalPointFiniteness` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedNearbyStrictLocalDescription` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedProductPointsConservative` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedProperFibreExchange` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedSourceLocalization` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.OrientedTripleLimitDescent` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.PsiConstructibilityDescent` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.QcqsOrientedTriplePresentation` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.Paper.StratifiedOrientedCover` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.TraceFormula.FiniteCoverTubeComparison` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.TraceFormula.GabberNearbyCycleDimensionBound` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointCohomology` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointNormalizedStratum` | unclaimed | Unchanged public API; no adaptation. |
| `Sheaf.TraceFormula.ProperBaseChangeCoherentConservative` | unclaimed | Unchanged public API; no adaptation. |

Unmodified copies of all three direct importing modules were compiled with
`lcompile.py` against the sandbox overlay; all pass.

No module held by another group is changed. The original and delivered public
bodies/signature were compared verbatim and agree. In particular, no statement
becomes stronger, weaker or different, and no target statement review is reopened.

## Status

landed 20261020T174812-L-799705 2026-10-20 (merge of deliver/K1/Sheaf.Paper.SitePointReconstructionSets)
