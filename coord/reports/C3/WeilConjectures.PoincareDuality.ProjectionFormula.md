## What changed

The change record `coord/changes/C3-projection-instance-caches.md` records this repair.

Removed the duplicate `CategoryTheory.ProjectionCache.scalar*` theorem declarations from
`Sheaf.Paper.IntegralResidueDerivedMonoidal`, as required by the return review. The proof
still uses that module's seven canonical structural caches through a private import and
local instance attributes. The three previously completed naturality proofs and all
upstream declaration heads remain unchanged. The item and the cache module compile cleanly.

## Proved and sorry left

The delivery closes these three original holes:

- `exceptionalProjectionMorphismOfCompactification_natural_right`;
- `boundedConstructibleExceptionalProjectionMorphism_natural_right`;
- `boundedConstructibleExceptionalProjectionMorphism_natural_left`.

The following two original holes remain, with no new holes added:

- `isIso_openImmersionProjectionComparison`;
- `isIso_boundedConstructibleExceptionalProjectionMorphism`.

The returned delivery's duplicate scalar theorem declarations were removed; they were not
new mathematical holes.

## No longer needed

The eleven duplicate `CategoryTheory.ProjectionCache.scalar*` declarations and their
local registrations are no longer needed. They duplicated declarations already present in
`Sheaf.Paper.CondensedFlatCoefficientCalculus` and were removed from the cache module.
The exploratory aliases and diagnostic files are outside the delivered `lean/` tree and are
not part of this delivery. No DAG node or existing proof dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned attempt introduced theorem declarations whose statements duplicated existing
library declarations word for word. The repair removes those declarations and keeps only
instance caches needed to keep elaboration under the file limit. The mathematical route and
the three closed proofs are unchanged.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
