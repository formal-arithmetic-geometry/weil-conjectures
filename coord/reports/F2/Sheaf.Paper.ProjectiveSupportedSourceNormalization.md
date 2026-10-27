## What changed

Replaced the parent proof with a short tensor and precomposition argument from the new untensored supported-arrow statement. Added `Sheaf.Paper.ProjectiveSupportedSourceArrow`, which records the strictly simpler arrow identity and its proof plan.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.RationalP1.supported_source_normalization`. Added one strictly simpler split theorem, `AlgebraicGeometry.ProEtale.RationalP1.supported_source_arrow`, with its proof plan as `sorry` (node `lem-sfb-projective-supported-source-arrow`).

## No longer needed

The former private derived-category comparison imports and helpers are no longer needed; the item now imports only `Sheaf.Paper.ProjectiveSupportedSourceArrow`.

## Where the brief, the DAG or earlier work was wrong

The parent target is a direct tensor consequence of the untensored arrow identity, but the latter requires the full ordinary-to-derived section comparison and was strictly simpler to state separately. No target statement was changed.

## New nodes

`lem-sfb-projective-supported-source-arrow` is the untensored supported source identity used by the parent. It is strictly simpler because it omits arbitrary precomposition by `singleUnitIso.inv` and tensoring by `M`. No change records are needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ProjectiveSupportedSourceArrow": "fc84156fa4d92be60b4c4eb579696db3aea155f1", "Sheaf.Paper.ProjectiveSupportedSourceNormalization": "69bc6c3b4a98dd6ad5edd30658c65b83dfa8620d"}, "results": {"Sheaf.Paper.ProjectiveSupportedSectionProjection": {"hash": "1f4e9827eddc9de852380fd0121d596fc2cea5e4", "status": "OK"}}, "seconds": 24, "time": "2026-10-28T07:12:45+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
