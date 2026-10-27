## What changed

Proved `Module.free_surjections_common_stabilization` in
`Sheaf.LinearAlgebra.FreeSurjectionsCommonStabilization`, preserving its statement and
following all four steps of `lem-trf-free-surjections-common-stabilization`.
Added only the proof import `Mathlib.LinearAlgebra.StdBasis` for the finite-function
free-module instances. The existing projectivity import supplies
`Module.Projective.of_free` and `Module.projective_lifting_property`, which give the
two lifts. Constructed the equivalence from sums, differences and products of linear
maps and its explicit inverse; checked both inverse identities, the commuting equation,
and both inclusions of the kernel image equality.

The cited existing declarations are Mathlib's `Module.Free.function`,
`Module.Projective.of_free`, and `Module.projective_lifting_property`, together with
linear-map product operations and equivalence inverse identities. No landed theorem
is copied or restated, and no definition or statement correction is proposed.
The DAG already describes this proof, so no node changes are required.

## Proved and sorry left

Closed the sole hole: `Module.free_surjections_common_stabilization`
(node `lem-trf-free-surjections-common-stabilization`).
Holes closed: 1. Holes added: 0. Sorries left in the delivered module: 0.
No split-off statements.

Validation: the delivered module compiled without errors or warnings via
`lcompile.py` in 2.7 seconds.

## No longer needed

None. All existing imports remain needed by the public statement or proof, and
all three declared proof dependencies are used. No nodes or modules are withdrawn.
Search of the local libraries and LeanFinder found ingredients, rather than an
existing theorem with the full explicit formulas and commuting kernel comparison.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The statement includes no nontriviality or positive-rank
assumption; the construction and cancellation proofs apply unchanged at zero rank,
for the zero module or ring, and in characteristic two.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
