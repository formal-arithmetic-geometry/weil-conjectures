## What changed

Restored `lean/Sheaf/Algebra/Homology/AffineTensorCohomologyLocalizationSquare.lean`
from its quarantine archive, preserving its complete proof, theorem signature,
public imports, and private proof imports. This repairs the assigned rework row:
the archived module had been removed after its realization dependency lacked a
compiled object. That dependency now has a complete implementation in the shared
source. An unchanged sandbox copy of it compiled in 5.4 seconds, followed by this
module in 8.0 seconds, with no errors or warnings. The unchanged dependency copy
was removed from the packet after compiling; it is not an adaptation.

The proof realizes both prescribed coefficient lifts on one functorial K-flat
resolution, applies the existing derived-localization cohomology isomorphism,
and transports the comparison square along tensor associativity. The source
and target naturality equations are proved by conjugation and cancellation of
isomorphisms. No data, statement, or proof route was changed.

Searches: Loogle `ModuleCat.extendScalarsComp` found the scalar-composition
isomorphism and its generator equation used by the archived proof. LeanFinder
`natural cohomology tensor localization comparison square flat extension of
scalars` returned localization and flatness infrastructure, with no theorem for
prescribed coefficient lifts. Local searches of both library roots confirmed
that `affineDirectLocalizedTensorSquare_core` concerns a scheme/stalk interface,
whereas the assigned theorem is the general prescribed-functor statement.
The existing dependency declarations already give its shortest available route.

## Proved and sorry left

The restored theorem
`RingTensorCohomology.affineTensorCohomology_localization_square`
(node `lem-pc-affine-tensor-cohomology-localization-square`) has a complete proof.
Its three private declarations are also complete. The archived module had zero
holes; the restored module has zero holes. Holes closed: none (0 of 0).
Holes added: none. Split off: none. This is a restoration, not a new proof or
a decomposition.

## No longer needed

None. All existing proof dependencies and imports are retained and used.
No module or DAG node is withdrawn. In particular the quarantined parent
`Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationIsos` still uses this
theorem, so the absence of live importers does not justify pruning it.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, rather than a live module with a remaining
`sorry`. The current rework row was read before restoring the archive.
The DAG attachment and proof plan agree with the archived Lean proof and are
preserved. No mathematical error or interface change was found. The missing
published realization object was handled for verification by compiling the
current unchanged dependency in the sandbox, rather than replacing its statement
or deleting the assigned module.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
