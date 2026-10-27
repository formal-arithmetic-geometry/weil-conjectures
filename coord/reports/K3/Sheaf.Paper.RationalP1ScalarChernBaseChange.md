## What changed

Restored the quarantined base-change module and decomposed its conjunction into two strict
component theorem obligations, then assembled the parent theorem by exact pairing. The
sandbox also carries the restored scalar Chern maps dependency for import-order compilation.

## Proved and sorry left

Closed `scalar_chern_base_change` by exact assembly. Added two strictly smaller named
obligations, each proving one conjunct:

- `scalar_chern_base_change_unit`
- `scalar_chern_base_change_chern`

## No longer needed

None. The scalar Chern maps import is required by all three declarations, and no planned
proof dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The prior source's build failure was caused by the quarantined `RationalP1ScalarChernMaps`
import. The parent proof plan was too coarse for the available geometric argument, so the
unit and Chern equations are recorded as separate strict component obligations.

## New nodes

- `lem-sfb-rational-p1-scalar-chern-base-change-unit-component`
- `lem-sfb-rational-p1-scalar-chern-base-change-chern-component`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernBaseChange": "2e619fb96d918c194ac32aef46d40e4abed4efe6", "Sheaf.Paper.RationalP1ScalarChernBaseChangeChern": "c43c3ddc9dcdcff5f854b753ce5547cc66dd917d", "Sheaf.Paper.RationalP1ScalarChernBaseChangeUnit": "34cab210b836965c862cf45b69fe96a18bb7f1be"}, "results": {}, "time": "2026-10-28T03:04:34+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
