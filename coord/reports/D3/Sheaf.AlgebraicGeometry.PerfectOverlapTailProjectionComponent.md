## What changed

Repaired `AlgebraicGeometry.perfectOverlapTailProjectionComponent` with its entire statement,
visibility and universes unchanged. The calculation works for an arbitrary containing open
and specializes to the two Boolean branches. It uses the existing restricted-composition,
composition-prism and cartesian-projection APIs, with naturality and inverse cancellation.
The repaired component compiled cleanly in 20.1 seconds in the current session.

`PerfectOverlapStageTransport` now constructs the same fixed transport directly, without
inserting casts by rewriting the two definitionally equal endpoint functors.
`DerivedPullback` keeps the original fixed chosen functor behind `derivedPullbackData`.
`derivedPullback_eq_choose` proves equality with the original choice, and
`derivedPullback_spec` exposes precisely its original properties. This prevents the kernel
from repeatedly expanding the large choice predicate when comparing functor fields.
No new choice of data, mathematical assumption or target signature is introduced.

The 71 implementation callers of the original choice specification now use that proved API.
Their existing public signatures and visibility remain identical. In the universe-comparison
caller the API receives the original explicit instances. The redundant implementation-level
`change` in `PicardSingleRankUnrestrictedPerfectChart` is removed. The affine tensor adapter
uses one direct witness elimination, and the affine model proof introduces the statement's
own fixed complex instead of reconstructing it. `BottomFreeChainDerivedSquare` reuses the
public open-pullback comparison, introduces the statement's own functors/complexes, and transports
the underived equivalence unit directly, avoiding derived adjointification. All these modules were unclaimed.

Change records: `coord/changes/D3-derived-pullback-data-boundary.md` and
`coord/changes/D3-stage-transport-direct.md`. The original implementation callers were
checked against the changed dependency and the adapted versions were compiled individually.
The final delivery checks compile the whole delivered set and inspect its axioms.

Validation: the original 74 delivered Lean modules passed the retained compile batch.
The additional `PerfectOverlapStageTransportComponent` adaptation removes its final `rfl`,
which now follows a rewriting step that already closes the goal. Its existing signature
and visibility stay identical; it is unclaimed. The complete current helper chain
(`PerfectOverlapStageTransportComponent`, `PerfectOverlapTailProjectionFactors`, and
`PerfectOverlapTailProjectionAt`) compiled in import order in 2.7, 7.1 and 6.9 seconds.
The repaired component theorem also passes an explicit axiom check, using only
`propext`, `Classical.choice`, and `Quot.sound`. This repairs a consumer introduced
since the previous retained attempt.
The original `PerfectOverlapTailProjectionFactors` from the current shared snapshot also
compiled unchanged against the repaired dependencies (6.2 seconds). Existing public signatures
and visibility were compared with the current shared sources: none changes. The only removed
declaration is the private duplicate `Scheme.openPullbackIso`. The required delivery commands
repeat the compile and axiom checks before pushing.

## Proved and sorry left

Current shared baseline: 0 holes in the assigned module; 0 holes closed and 0 added.
`AlgebraicGeometry.perfectOverlapTailProjectionComponent`
(node `lem-pc-perfect-overlap-tail-projection-component`) now has a complete direct proof.
The original ancestor had one hole, but the returned head already proves it through helper
modules: this delivery is a repair, and does not count that ancestor hole a second time.
Split-offs: 0. Holes remaining in all 75 delivered Lean modules: 0.
All supporting API declarations are proved; no proof is left for another worker.

## No longer needed

Removed the current direct proof import
`Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionAt`. The direct proof instead uses
`PerfectOverlapStageSchemeIso`, `PerfectHomCompositionPrism`,
`PerfectOverlapProjectionCompositeAbstract`, `PerfectOverlapRestrictedComposition`,
`PerfectOverlapNestedPullbackSquare` and `PerfectOverlapStageEquivalence`.
All seven original mathematical dependency nodes remain needed, directly or through these
existing comparison APIs; no unit statement or proof step is bypassed.

These eleven modules are no longer reached from this item, since the direct proof combines
its composition and projection equations without the returned helper chain:

- `Sheaf.AlgebraicGeometry.PerfectOverlapIsoCancelAbstract`
- `Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTwoFactors`
- `Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectFactors`
- `Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectTail`
- `Sheaf.AlgebraicGeometry.PerfectOverlapStageTransportComponent`
- `Sheaf.AlgebraicGeometry.PerfectOverlapTailNormalForm`
- `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionAbstract`
- `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionAt`
- `Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionFactors`
- `Sheaf.AlgebraicGeometry.PerfectOverlapTailRestrictedComposite`
- `Sheaf.AlgebraicGeometry.PerfectOverlapTailStageProjection`

These modules remain present and unchanged. In particular the named failing consumer
`PerfectOverlapTailProjectionFactors` was independently compiled against the repaired overlay.
The private duplicate `openPullbackIso` construction in `BottomFreeChainDerivedSquare` is
also no longer needed.

## Where the brief, the DAG or earlier work was wrong

The returned `PerfectOverlapTailProjectionFactors` proof attempted to rewrite a transport
component at a syntactically different open-inclusion proof. The repair avoids that
helper chain and proves the original component directly from the existing fixed-comparison APIs.
The retained monolithic attempt also exceeded the checker limit. Profiling isolated repeated
reduction of the chosen derived-pullback data; hiding exactly that existing construction,
with a proved equality/specification interface, resolves the component cost. The caller
adaptations are necessary because the old raw choice specification no longer unfolds
implicitly to that interface. No mathematical statement is disputed and the prescribed unit
route is retained. No target statement changes.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
