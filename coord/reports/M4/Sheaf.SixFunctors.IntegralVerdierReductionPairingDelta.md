## What changed

Filled `reductionPairing_delta` with the finite adjunction injectivity argument and added the
strictly lower uncurried mate statement
`reductionPairing_delta_uncurried` in a separate module. The assigned theorem imports that
statement and identifies its right hand side with the finite delta by unfolding
`restrictionDualDelta`.

## Proved and sorry left

`reductionPairing_delta` is proved. One sorry remains in the newly added declaration
`reductionPairing_delta_uncurried` (node
`lem-sf-integral-verdier-reduction-pairing-delta-uncurried`); it is the explicit evaluation
mate calculation described in its docstring.

## No longer needed

None. The proof uses the existing `IntegralVerdierModels` definitions and the new uncurried
mate node; no declared dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted a Lean-level declaration for the uncurried mate calculation.
The final curried equality is obtained by adjunction injectivity only after that calculation is
stated separately.

## New nodes

`lem-sf-integral-verdier-reduction-pairing-delta-uncurried` records the strict uncurried
evaluation identity and is implemented by
`Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta": "e3b727db22e8a97ccf4811eb97e53087f353632a", "Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried": "4912105f8926da8453321454f1a0a0fb9a670522"}, "results": {}, "time": "2026-10-28T07:12:01+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
