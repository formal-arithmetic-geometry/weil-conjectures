## What changed

Retired `Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap` in favor of its
existing source twin, following its depth-zero retirement entry and the human's
2026-10-20 instruction in `coord/changes/retire-sheaf-twins-20261020.md`.
Also withdrew its sole consumer,
`Sheaf.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation`: it is unclaimed,
has no importers, and none of its declarations has external uses. Both paths are
in `deleted.txt`. No new or modified Lean file remains in the packet.

The two consumer DAG records, `def-sc-cartesian-chart-restricted-raw-class` and
`lem-sc-cartesian-chart-restricted-map-evaluation`, now point to the existing
source module `WeilConjectures.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation`,
with its verbatim current signatures. No mathematical statement or proof route changes.
The assigned item's two lemma signatures and proofs match its source twin exactly
modulo whitespace. The consumer matches its source twin modulo whitespace after
switching its two Sheaf imports and removing three unused raw-class parameters.
Change record: `coord/changes/U2-retire-cartesian-chart-exchange-chart-map.md`.

Validation: complete source comparison; downstream and declaration-use searches;
no consumer remains for either withdrawn module. The first import-only adaptation
compiled standalone in 49.9 seconds, but timed out in the delivery check and in
profiling attempts. It is superseded by the final withdrawal packet: the consumer
is dead, so retaining and optimizing its duplicate construction is unnecessary.
No file or proof is split, and no compiler limit is raised.

## Proved and sorry left

The assigned item had zero sorries; the additional withdrawn consumer also had
zero. Zero holes closed, zero added, zero split off, zero left in delivered code.
No new mathematical proof is claimed.
The source twin retains the proved declarations
`AlgebraicGeometry.Etale.chartRestrictedMap_eq_rawAffine` (reflexivity) and
`AlgebraicGeometry.Etale.chartRestrictedMap_apply_eq_rawAffine` (congruence).
The consumer source twin retains the real construction
`AlgebraicGeometry.Etale.cartesianChartRestrictedRawClass`, its proved defining
equation `AlgebraicGeometry.Etale.cartesianChartRestrictedRawClass_eq`, and the
proved `AlgebraicGeometry.Etale.cartesianChartRestrictedCohomologyMap_eval`.
No source declaration is removed or replaced by an unfinished proof.

## No longer needed

Withdrawn modules:
- `Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap`.
- `Sheaf.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation`.

With the consumer's withdrawal, its private imports of
`Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap` and
`Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation` are removed.
No pruning of the latter module is claimed. The source twins and their dependencies
remain untouched. Both consumer nodes remain, attached to the source declarations;
no DAG node is deleted and no unit step is bypassed.
The assigned copy's imports of
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapBridge`,
`WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartSystem`, and
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeObjects` remain needed
by its source twin. The consumer twin retains imports of
`WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback`,
`WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyClass`,
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeEvaluation`, and
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeChartMap`.
No other module or proof dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open obligation, but the actual item is
a retirement entry with zero holes. Its assigned lemmas are already proved in
both roots. The consumer is now unused in the shared tree; the earlier bulk pass
had deferred the assigned item because of a pending consumer landing.
Its two node attachments still named the dead Sheaf consumer rather than the
source implementation. Only those Lean attachment records change.
The source raw-class construction omits unused U, r, hr parameters, so reusing
its verbatim signatures needs no adaptation after all users of the dead copy
are gone. No target, mathematical statement, or unit route changes.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
