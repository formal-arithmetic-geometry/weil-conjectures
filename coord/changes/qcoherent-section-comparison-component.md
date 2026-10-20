# AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionNatIso

## Reason

The Sheaf module and adopted source module declare the same public constants.
Combining the source normalization lemmas with the old Sheaf consumers fails
with `environment already contains ...moduleComparisonEquiv`. The item is
quarantined for this collision. Migrate its comparison dependencies to the
adopted source construction and its existing extension.

The duplicate Sheaf module is held by F2. This packet does not change or withdraw
that module. It migrates the five currently unclaimed live consumers instead:
CanonicalCoherentEtaleComparison, CoherentEtaleComparisonMorphismExists,
CoherentEtaleEffacingSequence, CoherentEtaleComparisonPullback and
CoherentPowerComparison. In the last four, only one private import changes.
Their declarations, signatures, attributes and proofs stay verbatim.

Both constructions use the same injective resolution, exact forgetting,
acyclic section comparison, explicit Hom-complex comparison and terminal-source
isomorphism. The source has two additional identity natural isomorphisms
`siteExtNatIso` and `siteHNatIso`; these do not change the map. Its
`siteSectionsNatIso` starts at evaluated cohomology, definitionally the same
Ext functor. The source extension supplies the same comparisonHasSheafify,
comparisonHasExt and sectionsComparisonNatIso API.

No adopted source-library file changes. Target semantic review reopens because
comparison definitions used by target statements now have the source owner.
No target statement or mathematical hypothesis changes.

## Old

In CanonicalCoherentEtaleComparison:

```lean
public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

In each of the four other unclaimed consumers:

```lean
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

The original item also imported this Sheaf compatibility module privately.

## New

In CanonicalCoherentEtaleComparison:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
```

In each of the four other unclaimed consumers:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
```

The item obtains these declarations from its public canonical-comparison import.
The node attachment identifies the existing adopted source owner. The duplicate
Sheaf module is left untouched for its current holder.

## Users

Names below are modules under `Sheaf.AlgebraicGeometry`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality | F2 | unchanged; migration avoids the duplicate |
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed | public imports select the adopted source owner |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists | unclaimed | one private import migrated |
| Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence | unclaimed | one private import migrated |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | unclaimed | one private import migrated |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | unclaimed | one private import migrated |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | Q2, quarantined | verification copy only |
| Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero | B2, new | uses source cocycle normalization |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | B2 | restores and proves quarantined item |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | A2, restored during session | forced removal of the duplicate private import |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed, restored | verification only; no adaptation delivered |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | F4, restored during session | forced duplicate-import removal and public statement import |

The repair service also restored QcoherentNormalizedPullbackSquare, held by F4,
at 2026-10-20T21:15:58Z. It must drop the private duplicate import for the same
reason as the Frobenius consumer. Its original additionally has a pre-existing
public-visibility error: its public statement uses moduleCohomologyFMap but imports
that module privately. The compiler requests a public import. The adaptation
promotes that existing import and removes the duplicate import; these are the only
two edited lines. All declarations, signatures, attributes, proofs and hypotheses
remain verbatim. The adapted file compiles. The cohomology-comparison and Frobenius
comparison verification copies are not delivered.

The pre-existing visibility failure is reported as such, not as an effect of the
new comparison definition. Both import edits are needed for this live consumer to
compile after its migration; neither is a mathematical interface change.

## Status

landed 20261020T230711-L-602865 2026-10-20 (merge of deliver/B2/Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison)
