## What changed

Repaired the returned decomposition by replacing the three independent existential component theorems with the pinned structure `PinnedCounitData`. It stores one `CounitData` together with its actual `ScalarNormalization` and `FrobeniusNormalization` witnesses, so the comparison, exchange, inverse exchange, and normalization fields are shared. The target theorem now projects all three clauses from one pinned witness. Restored the original seventeen-step proof imports, including `FiniteTorAmplitudeSites` for the field-stage definition used in Step 14.

## Proved and sorry left

The target `WeilConjectures.NativeWeilScalar.scalar_frobenius_counit` is proved by projection from one `PinnedCounitData`. One split theorem remains `sorry`: `native_pinned_counit_data_exists`, node `lem-sf-native-pinned-counit-data-existence`. Its statement is the pinned construction that the seventeen proof steps must establish; the projection of its fields to the target is complete.

## No longer needed

The three returned arbitrary-`CounitData` component modules and nodes were withdrawn because their universal quantification was false and their witnesses did not share pinned comparison data. The target retains the plan imports, including `Sheaf.Paper.FiniteTorAmplitudeSites`; no plan dependency was pruned in this repair.

## Where the brief, the DAG or earlier work was wrong

The earlier split quantified scalar and Frobenius normalizations over arbitrary `CounitData`, although `CounitData` does not pin `alpha`, `leftIdentification`, `exchange`, or `inverseExchange`. Those fields can be changed independently while preserving `CounitData`, breaking the normalization clauses. A single pinned datum is required so all three target clauses refer to the same normalized comparisons.

## New nodes

`def-sf-native-pinned-counit-data` records the pinned structure with shared fields. `lem-sf-native-pinned-counit-data-existence` records the single pinned counit datum whose fields are one `CounitData`, one scalar normalization for the given `P`, and one Frobenius normalization for that same datum. Its proof plan follows the original seventeen steps: finite-stage scalar mate normalization and cocycles, transport of the constructible adjunction, Frobenius exchange and inverse, mate invertibility, and the invariant counit identity. No arbitrary `CounitData` is quantified over.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativePinnedCounitData": "87f57d941325fd25d6f0a67e9b59b4b075da3cc7", "Sheaf.Paper.NativePinnedCounitDataExistence": "fc8521da6562f46554dfd8db4caa532ca3b7f1df", "Sheaf.Paper.NativeWeilScalarFrobeniusCounit": "55746e767fdf5357b95164ede55ec884ecf68439"}, "results": {}, "time": "2026-10-28T04:35:23+0800", "transitive": 0, "version": 1}
```

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
