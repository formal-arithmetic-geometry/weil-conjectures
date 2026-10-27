## What changed

Proved `WeilConjectures.PurStrictScalar.scalarLimitTensor_composition` in
`Sheaf.Paper.ScalarLimitTensorComposition`, preserving its signature. Added a private
proof import of `Sheaf.CategoryTheory.DerivedExactSquareCoherence` and proved local
helpers for the canonical square normalization and its horizontal composition.
Updated the item node to record the direct unit-normalization proof.
Validation: `lcompile.py` compiled the final module without warnings in 21.4 seconds;
the theorem signature is preserved verbatim and the proof import introduces no cycle.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.PurStrictScalar.scalarLimitTensor_composition`.
Holes closed: 1 of 1. Holes added: 0. No `sorry` remains in the item or is added elsewhere.
The proof uses the existing exactness and K-injective preservation theorem
`scalarLimitTensor_exact`; its unproved dependencies remain separate existing items.

## No longer needed

The proof does not use node `lem-pur-roos-comparison-horizontal-coherence`, module
`Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence`, or the theorem
`scalarRoosTensorNormalization`. No Roos calculation or localization of a Roos
comparison is needed: the definition of `scalarLimitTensor` itself has the universal
unit normalization. Removed the Roos-coherence proof dependency from the item node.
No existing import was removed; the public scalar-limit definitions import is retained.
No module is withdrawn, and no claim of global unreachability is made.

## Where the brief, the DAG or earlier work was wrong

The planned Roos route is valid but longer than necessary. The existing
`normalized_comp` and `normalized_naturality` lemmas establish coherence directly
from the specified derived units. The remaining ordinary limit identity follows
from naturality of alpha after each limit projection. No statement or definition
repair is required, and the unit route is preserved.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
