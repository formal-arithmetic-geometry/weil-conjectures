## What changed

Preserved the restored canonical source adapter and both public imports. Replaced the
proof of AlgebraicGeometry.openPullbackRestrictionIso_hom_app_eq_square_inv by a direct
application of Mathlib Iso.hom_eq_inv to the two component isomorphisms. Removed the
unnecessary file-wide synthInstance.maxSize and two respectTransparency overrides.
No source-library file, definition, public signature, instance binder or docstring changed.
The existing node now describes the direct component proof; all dependencies remain.
Change record: coord/changes/t7-core-comparisons-default-elaboration.md.

The original module compiled in 11.1 seconds. The final module compiled in 9.3 seconds
with default elaboration settings and no warnings. This timing is an observation, not a
performance guarantee. Both the declaration-use scan and the seven archived direct
consumers were inspected; their API is preserved. Their unrelated quarantine dependencies
are not claimed to compile in this delivery. The five DAG parents and unit route remain.

## Proved and sorry left

0 original holes; 0 closed; 0 added; 0 remaining; 0 split off. This is a zero-hole repair
item, not a new mathematical proof counted against the ledger. The four proved equations
remain at node def-pc-perfect-overlap-core-comparisons-api:

- AlgebraicGeometry.openPullbackRestrictionIso_inv_app_eq_square
- AlgebraicGeometry.openPullbackRestrictionIso_hom_app_eq_square_inv (simplified proof)
- AlgebraicGeometry.perfectOverlapRestrictionBeta_hom_app_square
- AlgebraicGeometry.perfectOverlapRestrictionBeta_inv_app_square

## No longer needed

No imports, modules, nodes or parent dependencies are removed. The three file-wide
elaboration overrides and the intermediate component-isomorphism reconstruction are
unnecessary. The source adapter and stage-equivalence API remain publicly imported.
No archived module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned rework row predates U9's restoration, which was reviewed and landed as
20261021T163831-L-1115476 before T7's claim at 2026-10-21T16:39:06Z. Consequently the
current item already has zero holes and compiles; it no longer exhibits the archived
global-build failure. This delivery does not claim to have performed that restoration.
It preserves that repair and simplifies the proof and elaboration configuration.
The independent reader should reconcile the stale rework entry with the prior landing.
The absence of live consumers is not evidence for withdrawal: seven archived consumers
and five DAG parents still require the attachment. No change to their mathematics is made.
LeanFinder, Loogle and grep were run via msearch.py; local Mathlib Iso.lean supplies the
exact Iso.hom_eq_inv lemma used in the proof.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
