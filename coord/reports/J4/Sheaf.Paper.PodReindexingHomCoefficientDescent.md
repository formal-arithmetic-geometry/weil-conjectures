## What changed

Proved `common_transposition` from the existing evaluation square, the transpose
characterization, and naturality of the recorded tensor comparison. Private,
proved helpers handle equality-only functor transport. No declaration signature,
public import, or definition interface changes. Updated proof Step 14 to describe
this argument. Local elaboration controls keep the large common-stage operation
constructions abstract. The advisory private-module linter is disabled for this
explicitly public module after profiling showed it dominated module-final linting;
the declaration signatures and proof kernel checks remain unchanged.

## Proved and sorry left

Closed 1 of the original 22 holes: `common_transposition` (namespace
`WeilConjectures.PodCoefficientDescent`). Added 0 holes and split off 0 statements.
The following 21 named theorem holes remain unchanged, all attached to
`lem-pod-reindexing-hom-coefficient-descent`:

- `ambient_reindex_scalar`
- `ambient_scalar_chain`
- `ambient_coordinates`
- `rational_transpose_existsUnique`
- `rational_signedShift_existsUnique`
- `rational_comparison_existsUnique`
- `integral_existsUnique`
- `integral_scalar`
- `rational_scalar`
- `integral_evaluation_transposition`
- `rational_evaluation_transposition`
- `rational_composition`
- `rational_pullbackShift_existsUnique`
- `rational_signed_shifts`
- `common_evaluation_existsUnique`
- `common_pair_permitted`
- `common_comparison_existsUnique`
- `common_evaluation`
- `common_transpose_existsUnique`
- `common_compositor_existsUnique`
- `common_composition`

## No longer needed

None. No imports, modules, or nodes are withdrawn. The existing unfinished
scalar, localization and common-stage obligations still need their recorded
routes. Transposition itself now uses the existing common evaluation square
rather than repeating its finite-field representative calculation.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The common transposition part of Step 14 admits
the shorter categorical argument above. A second argument for
`common_pair_permitted` compiled in isolation, but is not included in this packet
to keep this packet focused on the categorical transposition reduction. Its
integral-stage helper remains available in the sandbox scratch work. The original theorem and its proof plan remain in place.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
