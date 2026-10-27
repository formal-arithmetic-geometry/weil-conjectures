## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_endpoint_scalar_restrictions`
in `Sheaf.Paper.RingEndpointScalarRestrictions`, with its statement unchanged.
Added the proof-only import `Sheaf.Paper.ExceptionalRingTransportFamily`.
Applied `exists_exceptional_ring_transport_family` and
`ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core` to the canonical
proper compactification of the identity of W. Selected its endpoint scalar data.
Transferred those data from the lifted closure to the original two universes by
case analysis on ring stages; the actual functors, realizations, shifts,
additivity and exactness fields are retained. Reused every finite and integral
normalization. For identities, composed the scalar realization with the actual
coefficient equality and ambient multiplication tensor unitor, then lifted that
isomorphism through the fully faithful ring-stage inclusion. The image equation
is exactly the required multiplication normalization.
The private, fully proved `isAlgClosedOfEquiv` transports algebraic closedness
across fields in different universes. The split-off module
`Sheaf.Paper.RingEndpointScalarIdentityTransfer` contains the explicit four-case
scalar conversion and names the remaining normalized identity transfer.
Universe parameters on the record projections are explicit to avoid expensive
unification of maximum-universe expressions. Private transfer lemmas retain
finite equality/normalization and shift compatibility; private categorical
helpers construct the identity isomorphism without a costly universe conversion. Updated the theorem's proof docstring and
its node's proof, proof dependencies and proof origin to record this route.

The choice uses only W via its identity morphism, not an external geometric
operation or caller-supplied compactification. The identity is proper and
separated even for a nonseparated W; all finite-type hypotheses are already
present. The finite/integral stage cases are independent of the closure. Empty
schemes and residue exponent one require no extra assumptions or case exclusion.

## Proved and sorry left

Closed 1 hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_endpoint_scalar_restrictions`
(node `lem-sf-ring-endpoint-scalar-restrictions`).
Added one strictly smaller split-off obligation,
`WeilConjectures.ConstructibleExceptionalCoefficients.scalarIdentityAtClosure`
(node `lem-sf-ring-endpoint-scalar-identity-transfer`), in the new transfer module.
The item module itself has zero `sorry` declarations; the split module has one
named `sorry`.

The existing imported statements
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_exceptional_ring_transport_family`
and `WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core`
remain their separately assigned obligations. They are used through their stated
conclusions, with all input hypotheses supplied, and are not modified here.

## No longer needed

No existing Lean import was removed and no module is withdrawn.
The former direct proof dependencies
`lem-sf-exceptional-finite-scalar-mates`,
`lem-weil-finite-free-completed-scalar-comparison` are no longer separate
steps of this proof: the endpoint data are projected from the existing integral
mate record. Those modules still occur in the imported transport/mate development;
this delivery does not claim they are globally unnecessary.
The actual proof dependencies are
`lem-sf-exceptional-ring-transport-family` and
`lem-sf-exceptional-integral-scalar-mates-core`, and the split-off
`lem-sf-ring-endpoint-scalar-identity-transfer`.
The unit record has no separately realized statement or step that this route
would bypass. Neither dependency reaches this item's node or module.

## Where the brief, the DAG or earlier work was wrong

The shared snapshot retained a quarantine row and an old bad-import build log.
The live server queue instead lists this module as a stage-3 proof item, and its
live source contains the one theorem hole shown in the snapshot. The existing
coherent ring-transport family and integral scalar-mates core already provide
all of the endpoint data after specialization to the identity morphism. Thus the
old plan's separate preservation and normalization reconstruction is unnecessary.
No definition, public signature or attribute changed. The proof-only import of
the transfer module is required. The new node records the normalization substep
left for a subsequent worker.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RingEndpointScalarIdentityTransfer": "51582b2d492b509563501613f7a2a564eb763fe3", "Sheaf.Paper.RingEndpointScalarRestrictions": "d86aa1bf59db722ba3c8eb5e30436cce548c0963"}, "results": {"Sheaf.Paper.ExceptionalRingScalarMates": {"hash": "a23dbcf87e0a958ebf06e1b1678408ee15b08a63", "status": "OK"}}, "seconds": 33, "time": "2026-10-28T02:58:53+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
