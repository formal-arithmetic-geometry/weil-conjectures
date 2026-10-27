## What changed

Proved `bijective_and_isOpenMap_of_bijective_clopen_preimage` in
`Sheaf.Topology.ProfiniteClopenPullback`, preserving its complete signature, universes,
visibility, and imports. Clopen separation gives pointwise injectivity. The image is
closed by `Continuous.isClosedMap`, so a missing target point would have a clopen
neighbourhood with empty inverse image, contradicting injectivity of clopen pullback.
Surjectivity then identifies the image of each source clopen with its target clopen
preimage representative and proves uniqueness. The clopen basis criterion gives openness.
Updated the node's proof and proof origin to record this shorter closed-image argument.
No other module or definition changes.

The only declared proof dependency, `lem-weil-pbc-profinite-clopen-basis`, is used through
its Mathlib declarations `compact_exists_isClopen_in_isOpen` and
`isTopologicalBasis_isClopen`. Fresh leanfinder, loogle and grep searches found no complete
criterion already available. Read the node, its dependency, the unit record and source,
and Stacks `topology.tex` Tag 08ZZ. The unit route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`bijective_and_isOpenMap_of_bijective_clopen_preimage`
(node `lem-sfb-profinite-clopen-pullback-bijective-open`).
No sorry remains and no holes were added or split off.
The assigned file compiles cleanly through `lcompile.py`.
The proof makes no nonemptiness assumption and handles empty spaces, empty clopens,
and the empty open set through the same arguments.

## No longer needed

None. No imports, nodes or modules are removed. The existing Mathlib clopen-basis
proof dependency remains necessary. Only the explicit finite-subcover bookkeeping is
replaced by Mathlib's closed-image theorem; no project dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The DAG's surjectivity step can
be shortened using the closedness of the image, without changing the conclusion or
bypassing the unit route. No interface repairs or forced adaptations are required.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
