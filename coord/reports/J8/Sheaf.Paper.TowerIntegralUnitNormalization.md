## What changed

Added the pointwise comparison module `Sheaf.Paper.TowerIntegralUnitNormalizationComponents` and imported it privately in the assigned module. The assigned categorical theorem is proved by extensionality from the pointwise comparison.

## Proved and sorry left

The theorem `integralInverseSystem_unit_normalization` is proved. One strictly lower theorem remains as a split proof obligation: `integralInverseSystem_unit_normalization_components` in node `lem-sp-tower-integral-unit-normalization-components`.

## No longer needed

No imports or declared proof dependencies were removed. The assigned node now depends on the pointwise comparison node.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof step stated the levelwise coefficient comparison but did not expose it as a Lean declaration. The categorical conclusion is a short extensionality argument once that lower pointwise statement is named.

## New nodes

`lem-sp-tower-integral-unit-normalization-components` records the levelwise, chartwise, sectionwise coefficient-unit comparison and its remaining proof obligation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerIntegralUnitNormalization": "43ee5bde39cb236a1118664b030c088bc97cdefb", "Sheaf.Paper.TowerIntegralUnitNormalizationComponents": "aa967ae9da236da379d4ad68a893970b792e884e"}, "results": {}, "time": "2026-10-28T05:19:33+0800", "transitive": 0, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
