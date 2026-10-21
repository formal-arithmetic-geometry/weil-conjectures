## What changed

Filled the proof of `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorPullback`
in `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`. Apply Mathlib's
isomorphism invariance of quasi-coherence to the inverse of the component of the
existing canonical `tensorOrdinaryPullbackIso`, starting from the proved upstream
`isQuasicoherent_pullback g F`. This implements the existing docstring's argument
and node statement without changing the canonical comparison, signatures,
attributes, imports, or the unit route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorPullback`
(node `def-weil-pbc-tensor-pullback-ordinary-comparison`).
No sorry remains in the item. No holes or split-off statements were added.
The existing `tensorOrdinaryPullbackIso` definition is unchanged.

## No longer needed

None. Both existing public imports remain necessary for the canonical comparison
and the quasi-coherent pullback theorem. All dependencies named by the node's
statement retain their roles. No node or module is withdrawn, and no new proof
imports are required.

## Where the brief, the DAG or earlier work was wrong

None. The stated ordinary-pullback quasi-coherence theorem is already fully
proved upstream, and Mathlib supplies isomorphism invariance. The existing
canonical comparison is exactly the comparison needed for transport.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
