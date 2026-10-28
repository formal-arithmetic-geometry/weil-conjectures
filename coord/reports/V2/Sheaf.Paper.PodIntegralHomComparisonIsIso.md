## What changed

Added `Sheaf.Paper.PodIntegralHomComparisonComparisonIdentification`, which states the normalization identification needed by the target. The target module now imports this statement and proves `podIntegralHomComparison_isIso` by rewriting to the component of the normalized comparison and using its `IsIso` instance.

## Proved and sorry left

`podIntegralHomComparison_isIso` is proved. The split-off theorem `podIntegralHomComparison_eq_integralComparison` remains a named `sorry`, with node `stage3-derived-automorphism-continuation-a-integral-comparison-identification`.

## No longer needed

No imports or declared proof dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original item had no available Lean reduction of the normalization step. The DAG proof plan treats the identification of the normalized integral comparison with the evaluation-defined map as implicit; it is recorded explicitly as a strict intermediate statement here.

## New nodes

`stage3-derived-automorphism-continuation-a-integral-comparison-identification` records the normalization identification in the new module.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodIntegralHomComparisonComparisonIdentification": "7b065d7baf086ae6f3346849f8280295eccfc6f5", "Sheaf.Paper.PodIntegralHomComparisonIsIso": "37d069234f7c2d928409d0e2fc5dd6fe1d622b2c"}, "results": {}, "time": "2026-10-28T09:53:23+0800", "transitive": 0, "version": 1}
```

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
