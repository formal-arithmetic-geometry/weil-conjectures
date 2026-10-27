## What changed

Filled the five postponed proofs in `Sheaf.Paper.EvenLineProductIntegrationMaps`.
The block square follows from the polynomial-coordinate universal property of iterated
relative affine lines. The inverse coordinate permutation gives the specified geometric
isomorphism. Finite étale Tate-line local triviality gives constructible finite Tor
amplitude, preserved by tensor powers and inverse image; this supplies both origin
statements. The published fixed-scalar compact-support projection formula, composed
with the specified signed symmetries, proves invertibility of the coefficient-first map.

Added proved private helpers and private proof imports only. The generic finite-ring
line argument and generic tensor-power induction keep coefficient arithmetic out
of repeated derived-category elaboration. Updated the existing
node's proof, proof dependencies and proof origin. Public signatures, definitions and
public imports are unchanged. The unit's route is retained.

## Proved and sorry left

Closed five original holes, all in namespace
`AlgebraicGeometry.ProEtale.EvenLineProduct`:

- `block_geometry`
- `external_origin`
- `coordinate_geometry`
- `coordinate_origins`
- `projection_isIso`

No holes added, no split-off statements, and zero `sorry` remain in the item.

## No longer needed

No original imports, declarations, nodes or modules are withdrawn. Removed the
redundant private import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison`;
the private projection-formula import already exposes its finite-Tor API. The existing
statement dependencies remain needed by the concrete definitions. No unused part
of the unit route is bypassed. The proof uses existing fixed-scalar ordinary and
pro-étale derived-category results directly; it needs no intrinsic-coefficient
transport, new purity theorem, or supplied six-functor datum.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan despite the five explicit geometric and applicability
obligations in its Lean module. Its existing theorem docstrings give the argument;
the updated proof record makes that argument and the actual library route explicit.
The existing source-library finite-Tor closure and compact-support projection results
apply before specialization to the separate intrinsic-coefficient interfaces.
No mathematical statement or definition repair was necessary.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
