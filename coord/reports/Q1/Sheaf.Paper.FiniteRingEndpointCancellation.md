## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.finiteFixedEndpointCancellation`
with its original signature. The private, proved helper `cancel_endpoint_coordinates`
performs the categorical calculation: naturality of the proper compositor moves the
source open coordinate; cancellation removes the target open coordinate; naturality
of the direct-image comparison moves the inverse fixed proper/open comparison.
The existing `finiteFixedPushIso_composition` and the two instances of
`finiteFixedEndpointModelAt` then identify the resulting word. Expanding only the
refinement definitions and normalizing isomorphism association recovers exactly
`FrobeniusExchange.intrinsicRefinement`.

The item's DAG proof now records these operations. The statement, definitions,
public imports, and unit route are preserved. Local irreducibility annotations keep
the categorical normalization from unfolding large derived constructions. No other
existing module is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.finiteFixedEndpointCancellation`
(node `lem-sf-finite-ring-endpoint-cancellation`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-off statements or new axioms are introduced.

## No longer needed

None. All original imports and all three stated proof dependencies are used.
The endpoint and compositor statements already supply the required mathematics;
no further decomposition is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing plan closes the obligation
by categorical naturality and inverse cancellation. The proof uses the public
definition of `intrinsicRefinement`, so it does not need access to the private
`recordedRefinementCore` or `recordedCore_intrinsic` declarations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteRingEndpointCancellation": "a2e1d6509313e7cf07ec3955ace11a11137041a1"}, "results": {"Sheaf.Paper.FiniteRingRefinementCoordinatesCore": {"hash": "1b066b8c1de4ce2ce7cd228ed7eb9f2b58ed65d2", "status": "OK"}}, "seconds": 28, "time": "2026-10-28T14:52:44+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
