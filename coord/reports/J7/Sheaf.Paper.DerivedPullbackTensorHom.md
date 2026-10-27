## What changed

Proved `rationalPullbackScalarComparison_existsUnique` using the normalized integral
pullback comparison, scalar completion maps, and tensor induction. Added three private
proved helpers for categorical conjugation, heterogeneous functor maps, and raw scalar
localization isomorphisms. Existing public declarations, definitions and imports remain
unchanged.

## Proved and sorry left

Closed one original hole: `rationalPullbackScalarComparison_existsUnique`.
Added no holes and split off no statements. All remaining holes have node
`def-weil-derived-pullback-tensor-hom`. The seven original holes remaining are:

- `rationalDerivedPullback_existsUnique`
- `rationalDerivedTensor_existsUnique`
- `rationalDerivedInternalHom_existsUnique`
- `rationalTensorScalarComparison_existsUnique`
- `commonStageDerivedPullback_existsUnique`
- `commonStageDerivedTensor_existsUnique`
- `commonStageDerivedInternalHom_existsUnique`

## No longer needed

None. No imports, nodes, or modules were removed.

## Where the brief, the DAG or earlier work was wrong

The item node has an empty proof-step list. The proof follows the declaration docstring
using existing normalized integral and scalar-extension specifications.

The tensor scalar comparison was proved in an isolated scratch check, but adding it
to this module exceeded the 60-second compile limit. It is not part of this delivery.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
