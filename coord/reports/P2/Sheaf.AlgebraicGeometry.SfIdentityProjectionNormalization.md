## What changed

Filled `AlgebraicGeometry.Etale.SupportedTrace.identityProjectionNormalization` with the
canonical identity calculation already described by its node. The proof uses the proved
private `identity_pullback_tensor`, `normalized_identity_projection`, and
`derived_identity_conjugate` helpers from the stated dependencies, then transports the
ordinary projection through the existing proper projection-coincidence square.

A proved private categorical helper, `exact_comparison_naturality`, identifies right
derivation of a natural isomorphism with its exact-functor derived comparison. Applied
to `lowerStarId`, it identifies the two constructions of the specified identity
comparison. The final argument uses naturality and cancellation of isomorphisms.
A second proved private helper, `transport_identity_projection`, performs the
naturality and cancellation in an arbitrary category, keeping the derived-functor
wrappers out of rewrite matching. The completed proof compiled in 6.3 seconds before
line wrapping; the delivery verifies the formatted version and axiom dependencies.

All new imports are private proof imports; statements and definitions are unchanged.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.Etale.SupportedTrace.identityProjectionNormalization`
(node `lem-sf-identity-projection-normalization`). No holes added or split off.
No `sorry` remains in the item module.

## No longer needed

None. All three declared proof dependencies are used: the identity tensor calculation
from `SfEtaleGraphTransferTensor`, the categorical projection normalization and identity
conjugate from `SfGraphFirstProjectionSquare`, and the native proper projection square
from `ProjectionFormulaCoherence`. No module is withdrawn and no unit route changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing proof plan supplies the complete
argument; its right-derived/exact-comparison naturality step is now a proved local
helper rather than a further split. The item statement and its chosen comparisons are
preserved verbatim.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
