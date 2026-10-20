## What changed

Restored `lean/Sheaf/AlgebraicGeometry/BottomChainModelPullbackTransport.lean` from its
quarantine archive. Its stale public import of `Sheaf.AlgebraicGeometry.DerivedPullback`
was replaced by the adopted canonical upstream import
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, resolving the environment collision
recorded in `coord/rework.tsv`. The complete proof and theorem signature are preserved.
A declaration-local `maxHeartbeats 800000` setting, with an explanatory comment, is
required for elaboration of the categorical natural comparison; the file compiles in
under the 60-second limit. No target statement, definition, or public declaration was
changed. The change record is `coord/changes/C1-bottom-chain-pullback-upstream-restoration.md`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport` is fully proved from
the localized perfect pullback model, natural perfect counit, and universe-aware open
restriction comparison. Its private `compose_squares` helper is also proved. There are
zero `sorry`s before and after: holes closed 0, holes added 0, holes remaining 0.
No split-off theorem is needed.

## No longer needed

The retired `Sheaf.AlgebraicGeometry.DerivedPullback` import is no longer needed and
was replaced by the canonical upstream module. No proof dependency, node, or module is
pruned: the four recorded proof dependencies remain necessary to construct and transport
the specified morphism square.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined by the upstream synchronization because it imported a retired
Sheaf implementation that collided with the adopted source-library declaration; the
archive was not withdrawn and already contained a complete proof. The default heartbeat
budget is too small for this proof's categorical elaboration, although compilation is
well within the file timeout. The DAG statement and proof route remain correct. Searches
in the project and LeanFinder found only generic derived-category and homology tools, so
there is no shorter replacement route.

## New nodes

None.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
