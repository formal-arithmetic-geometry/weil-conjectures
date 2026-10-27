## What changed

Proved `AlgebraicGeometry.ProEtale.exists_orderedSpectralLattices` in
`Sheaf.Paper.OrderedSpectralLattices` with its original signature.
Finite dimensionality gives a small algebra model. Explicit spectral-norm-preserving
coefficient equivalences transport the existing stratified lattice theorem back to E.
The ordered common refinement is realized by fibre products, providing actual maps
into the old strata rather than inferring scheme factorization from image containment.
Pullback preserves local freeness and monicity; the ordinary scalar-unit identity
proves invertibility of the adjoint of the very inclusion constructed.

The complete proof compiled in 23.2 seconds in the final profiled check.
Private predicates name the repeated stratified and ordered lattice propositions;
this keeps the source theorem specialization from repeatedly expanding its dependent
coefficient-module statement during kernel checking. Profiling options are removed.

All added imports are proof-only. The existing ordinaryScalarUnit and finite-free
transport helpers are reused through import all. The node records this additional
proved comparison dependency. No public definitions or statements were changed.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.ProEtale.exists_orderedSpectralLattices`
(node `lem-sfb-ordered-spectral-lattices`).
Original holes: 1. Holes closed: 1. Holes added: 0. Holes left in the item: 0.
No split-off statements and no definition holes.

## No longer needed

The proof does not use `sk-prop-sfb-cartesian-coefficients` or its module
`Sheaf.Paper.CartesianCoefficients`: finite-limit preservation and the invertible
coefficient pullback map are supplied directly by the canonical module pullback API.
This node is removed from the item's proof dependencies. No imports were removed
from the original module. The unit's stratified-lattice route is retained.
No source-library declarations, modules, or public imports are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The actual pullback compatibility was already
proved as the general private ordinaryScalarUnit helper in
`Sheaf.Paper.IntegralResiduePullOrdinaryUnit`; the node now records its reuse.
The distinction between normalized lisseness and the raw locally-free cover predicate
requires the invertible coefficient pullback comparison, implemented explicitly here.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
