## What changed

Proved `WeilConjectures.sfFiniteOperations_intrinsicExceptionalBounds` in
`Sheaf.Paper.ExceptionalFiniteIntrinsicBounds`, with its signature unchanged.
The existing upstream `ProEtale.exists_preservationClauses` packages the affine-chart
argument with bounds independent of the finite coefficient ring. The proof identifies
its exceptional functor with the specified-compactification right adjoint by uniqueness,
then transports constructibility, arbitrary cohomological intervals, and Tor amplitude
through the canonical exact coefficient realization. Four proved private helpers handle
bounded support, constructibility, intervals, and isomorphism invariance of Tor amplitude.
The node's proof, proof dependencies and proof origin follow this implementation.
All added imports are private proof imports; no other module or public interface changes.
The complete proof compiled without warnings in 10.8 seconds before removing the
redundant direct finite-type import; delivery validates the final import set again.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.sfFiniteOperations_intrinsicExceptionalBounds`
(node `lem-sf-finite-intrinsic-exceptional-bounds`).
No holes remain in the item. No holes were added and no statements were split off.

## No longer needed

The separate planned uses of `lem-sf-class-compact-support-comparison` and
`lem-sf-proetale-constructible-origin` are unnecessary as direct dependencies:
the upstream preservation theorem already carries out the etale/pro-etale comparison,
and the arbitrary finite-ring constructible-derived-origin API gives the intrinsic
coefficient comparison directly. Their modules are not added as direct proof imports.
They remain available wherever other library declarations need them; no module is withdrawn.
The additional direct import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` was redundant with
existing public imports and is removed during cleanup. No original import is removed.
No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier searches missed the existing coefficient-independent
`AlgebraicGeometry.ProEtale.exists_preservationClauses` theorem. It already includes
unordered cohomological intervals, so the current proof needs neither a new geometric
chart-existence statement nor a separate inverted-interval case. Its geometric constants
also work for empty source. No mathematical statement or definition was changed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
