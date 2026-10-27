## What changed

Proved `integralProperTowerTransition` by composing two strictly simpler transition identities. Added proof-only imports of `IntegralProperTowerTransitionCore` and `IntegralProperTowerTransitionDirect`. The core and direct transport identities are split into their own modules with named DAG nodes.

## Proved and sorry left

Closed the original hole in `WeilConjectures.IntegralSystemRealization.integralProperTowerTransition`. Added two split-off holes, `normalizedTowerEvaluationTransition` (node `lem-sf-integral-proper-tower-transition-core`) and `directImageEvaluationTransition` (node `lem-sf-integral-proper-tower-transition-direct`).

## No longer needed

None; the canonical bridge remains the statement import and the two split modules are required by the proof.

## Where the brief, the DAG or earlier work was wrong

The original module depended on the unavailable proof of the full normalized tower/direct-image compatibility. The proof decomposes this into the normalized evaluation-transition identity and the finite direct-image transport identity; both are strictly lower-level statements.

## New nodes

`lem-sf-integral-proper-tower-transition-core` records the normalized tower transition evaluation identity; its module is `lean/Sheaf/SixFunctors/IntegralProperTowerTransitionCore.lean`.

`lem-sf-integral-proper-tower-transition-direct` records the scalar-restricted finite direct-image transition transport; its module is `lean/Sheaf/SixFunctors/IntegralProperTowerTransitionDirect.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralProperTowerTransition": "f7511aef518b98b4df4dc50abe7360fce28685ba", "Sheaf.SixFunctors.IntegralProperTowerTransitionCore": "8707a30d995ec39cea09b160b9f56a7f5c60f23e", "Sheaf.SixFunctors.IntegralProperTowerTransitionDirect": "bcbce4909c238032e6695a1b4498ce93070e9ba8"}, "results": {}, "time": "2026-10-28T01:12:01+0800", "transitive": 0, "version": 1}
```

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
