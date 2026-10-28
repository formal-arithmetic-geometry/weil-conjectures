## What changed

Proved `WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_endpoint_reconstruction`
in `Sheaf.Paper.ExceptionalTransportEndpointReconstruction`, preserving its exact signature and
its public import. Added only private proved helpers and three proof imports:
`Sheaf.Paper.SfDerivedCompleteLegacyComparison`, `Sheaf.Paper.FiniteCtfTriangulated`, and
`Mathlib.Data.Nat.Prime.Infinite`.

The existing arbitrary-scheme reconstruction theorem supplies the actual invertible unit and
counit. The proof identifies the integral finite-Tor predicate with complete objects whose
reduction has the required sequence bounds, restricts both functors and the adjunction, and
constructs every field of `Reconstruction`. The restriction retains the exact reduction,
limit, unit, counit and evaluations. No reconstruction data are chosen from a new existence
assumption, and no statement or definition is weakened.

Updated the item's DAG proof, proof dependencies and proof origin to match this argument.
The unit route is preserved. The proof applies to arbitrary schemes, including the empty
scheme, and retains each original cohomological and Tor endpoint without enlargement.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_endpoint_reconstruction`
(node `new-lem-sf-exceptional-ring-transport-endpoint-reconstruction`).
There are zero remaining holes in the item, zero holes added, and zero split-off statements.
All six new private lemmas are completely proved. Existing dependencies retain their own
proof obligations; this delivery does not claim their transitive axiom closure is complete.

## No longer needed

No imports were removed and no modules were withdrawn. The general three-endpoint transported
adjunction calculus theorem `purNormalizedReconstructionAdjunctionCalculus` is unnecessary for
this endpoint existence proof. Its module remains in the public statement dependency closure
because it provides the reconstruction interface. The narrower already-proved
`purNormalizedReconstructionOfScheme` supplies the required reconstruction fact directly.
No other nodes or modules are pruned, and no blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier node did not explain how the two differently presented completeness and boundedness
predicates agree. The proof makes those identifications explicitly, using the existing legacy
completeness comparison and derived cohomology vanishing criteria. The geometric invertibility
binder of `purNormalizedReconstruction` is not available in this item's signature; the existing
`purNormalizedReconstructionOfScheme` correctly omits it and proves exactly the needed fact.
The chain needs no further decomposition.

Validation: `lcompile.py` compiled the delivered module without warnings in 10.7 seconds,
within the 60-second per-file limit. No dependency file was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalTransportEndpointReconstruction": "5b7e0c7b9577f8591796fe4e5ecec8d26ff27ba3"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCoreReconstruction": {"hash": "f4d71239a5c408af93197d8db822ef4effc14990", "status": "OK"}}, "seconds": 213, "time": "2026-10-28T10:19:22+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
