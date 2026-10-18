## What changed

Proved `CategoryTheory.slice_site_localization` through explicit covering and pullback
transport on `Over` categories and the continuity API. Added
`Sheaf.CategoryTheory.Sites.SliceSheafInverseImageEquivalence`, whose intermediate
remainder theorem packages the slice inverse-image finite-limit and comparison clauses.

## Proved and sorry left

Closed `CategoryTheory.slice_site_localization` (one sorry). Added one strictly smaller
intermediate theorem, `CategoryTheory.sliceSheafInverseImage_remainder`, whose proof remains
`sorry` and is recorded by node `stage3-slice-sheaf-inverse-image-equivalence`.

## No longer needed

No imports were removed. The proof uses all original dependency declarations needed for
covering transport, continuity, and the slice equivalence.

## Where the brief, the DAG or earlier work was wrong

The original five-step proof plan leaves the categorical slice equivalence as a substantial
independent construction. It is therefore split into one intermediate statement rather than
left as an anonymous partial proof.

## New nodes

`stage3-slice-sheaf-inverse-image-equivalence` records the intermediate finite-limit and
comparison result in `lean/Sheaf/CategoryTheory/Sites/SliceSheafInverseImageEquivalence.lean`.
The change record is `coord/changes/sliceSheafInverseImage_remainder.md`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
