## What changed

Restored `Sheaf.SixFunctors.IntegralVerdierReductionPairing` and replaced its proof hole by a real conjunction proof. The two substantial conjuncts are split into the named public intermediate theorems `reductionPairing_transition` and `reductionPairing_delta`, each in its own module and imported privately by the item. Both intermediate theorem bodies remain `sorry` because their model-level calculations are the strictly simpler unresolved steps of the blueprint proof.

## Proved and sorry left

The item theorem `WeilConjectures.IntegralVerdier.reductionPairing` is proved from the two named intermediate statements. Two sorries were added as genuine split-off obligations: `WeilConjectures.IntegralVerdier.reductionPairing_transition` (node `lem-sf-integral-verdier-reduction-pairing-transition`) and `WeilConjectures.IntegralVerdier.reductionPairing_delta` (node `lem-sf-integral-verdier-reduction-pairing-delta`).

## No longer needed

None. The item retains its public import of `Sheaf.SixFunctors.IntegralVerdierModels`; the proof-only imports are the two split modules. All five declared proof dependencies remain represented in the corresponding split theorem nodes.

## Where the brief, the DAG or earlier work was wrong

The current rework/build record reports a bad import of `Sheaf.SixFunctors.IntegralVerdierModels`, but the restored module compiles against the current published artifacts. The original theorem proof was an unstructured `sorry`; the delivery makes the planned two-step decomposition explicit. No target statement or existing definition was changed.

## New nodes

`lem-sf-integral-verdier-reduction-pairing-transition` records the first, finite-transition/evaluation conjunct and its model-level proof obligation.

`lem-sf-integral-verdier-reduction-pairing-delta` records the second, reduction/delta conjunct and its model-level proof obligation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralVerdierReductionPairing": "58c56be144a113d9466062fc6e01ba30e3ef2e28", "Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta": "b43f4590c1c6501deaf42a8ebc362f1911d36c0e", "Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition": "d4796aab6920deef1e65b249613bf2fb0ed597db"}, "results": {}, "time": "2026-10-28T00:09:20+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
