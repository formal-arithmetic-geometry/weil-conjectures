## What changed

Replaced the assigned theorem's `sorry` with a complete transitivity proof. The proof
uses the new intermediate theorem
`normalized_integral_scalar_unit_underlying_bridge` and the identity clause of
`CompletedLineTensor.canonical_restriction`.

Added `Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge`, which records the
strictly simpler comparison with the completed tensor unit. Its statement retains the
scalar-object, realization-comparison, and identity-normalization hypotheses and
removes the final intrinsic-unit restriction step.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_integral_scalar_unit_underlying`.
One intermediate hole remains in
`WeilConjectures.ConstructibleExceptionalCoefficients.normalized_integral_scalar_unit_underlying_bridge`.
The bridge theorem is a strict reduction: the target's intrinsic
`sfIntegralScalarUnit` component is replaced by the corresponding completed
`CompletedLineTensor.unit` component, and the assigned theorem combines it with the
proved canonical restriction identity.

## No longer needed

The assigned module no longer directly imports `Sheaf.Paper.CompletedLineTensorCoherence`;
the bridge module supplies that public import. The target no longer needs the former
K-flat helper and ordinary-unit proof imports from the exploratory route.

## Where the brief, the DAG or earlier work was wrong

The original proof plan left the completed-unit comparison implicit. Directly
rewriting the normalized equation crosses two derived-category presentations with
different derived-category instances, so it cannot be made into a short proof in the
assigned file. The bridge isolates precisely that comparison for a separate proof,
while the assigned theorem now compiles quickly and only performs the canonical
restriction step.

## New nodes

`lem-sf-normalized-integral-scalar-unit-underlying-bridge` records the intermediate
completed-unit comparison in
`Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NormalizedIntegralScalarUnitUnderlying": "de545aa621a42cbb1029668adc2a72d776f2a340", "Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge": "c51a88f44d30e433b3bf18d0ab7e93087b2b4ad7"}, "results": {"Sheaf.Paper.NormalizedIntegralScalarUnit": {"hash": "ab8b5941851b42eca5e04b1d878d8e2845daa1b8", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T02:51:34+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
