## What changed

Filled `WeilConjectures.LocallyFiniteAdicCompactSupport.native_completed_coefficient_change`.
The proof obtains a pullback-compatible family of completed-to-native maps together with
one normalized coefficient presentation at each scheme, packages that family as
`PurCompactSupport.Change`, and uses presentation independence to prove the required
formula for every `CoefficientPresentation`.

Two genuine proof steps that require the finite-quotient and pointwise realization
argument were split into named intermediate theorems with DAG nodes. The item and all
three modules compile in import order with the prescribed launcher. The interface change is
documented in `coord/changes/NativeCompletedCoefficientChange.md`.

## Proved and sorry left

Closed the original sorry in `native_completed_coefficient_change` (1 of 1). Added the
following two strictly smaller named theorem sorries:

- `native_completed_coefficient_change_data`: construction of a pullback-compatible map
  family and one normalized presentation at every scheme.
- `coefficientPresentation_integralMap_eq`: equality of the integral maps of two
  normalized presentations by finite-quotient joint monicity.

## No longer needed

The proof does not use the separately planned
`lem-weil-pbc-continuous-coefficient-realizations` route; the pointwise realization
construction is isolated in `native_completed_coefficient_change_data`. No other
imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan bundled the map construction, pullback compatibility, and
presentation independence into one theorem. The implementation separates these as the
two intermediate nodes above so the completed theorem is assembled from proper
substeps rather than moving the original obligation under another name.

## New nodes

- `lem-sf-native-completed-coefficient-change-data`
- `lem-sf-coefficient-presentation-integral-map-independence`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientPresentationIntegralMapIndependence": "15107efc249843a670d06dbe8602e4e42592aa97", "Sheaf.Paper.NativeCompletedCoefficientChange": "277e7cbeb0467433b49e5789c3091a27c160a0ca", "Sheaf.Paper.NativeCompletedCoefficientChangeData": "f17d31a55a602189f3a2b4abc487f7cee5335f25"}, "results": {}, "time": "2026-10-28T04:20:21+0800", "transitive": 0, "version": 1}
```

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
