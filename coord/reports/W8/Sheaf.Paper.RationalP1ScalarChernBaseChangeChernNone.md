## What changed

Proved `scalar_chern_base_change_chern_none` by deriving the unit hypotheses for `Y` and
`ProjectiveLine Y`, obtaining the canonical normalized completed Chern pair, replacing the
arbitrary normalized inputs using `completedChernNormalized_unique`, and applying the
canonical closure-coefficient exchange statement. Added the proof-only imports for the two
split obligations. The target node proof dependencies now match this route.

## Proved and sorry left

The target declaration `scalar_chern_base_change_chern_none` is proved with no `sorry`.
The delivery adds the strictly lower split obligations
`completedChernNormalized_unique` and
`scalar_chern_base_change_chern_none_canonical`; both remain named `sorry` theorems because
the completed uniqueness argument and the geometric closure exchange are independent
remaining steps.

## No longer needed

The target proof no longer directly imports or cites the original geometric proof-plan
nodes. Their role is represented by the canonical exchange split obligation; the public
`RationalP1ScalarChernMaps` import remains needed for the target statement.

## Where the brief, the DAG or earlier work was wrong

The DAG's single geometric step is too large to close from the available declarations in this
session. It conflates existence of normalized completed Chern lifts, uniqueness of those lifts,
and the closure-coefficient exchange mate. These are now separate, strictly smaller
statements, with a real specialization proof assembling them.

## New nodes

`lem-sfb-rational-p1-completed-chern-normalized-unique` records uniqueness of a normalized
completed Chern adjunct.

`lem-sfb-rational-p1-scalar-chern-base-change-chern-none-canonical` records the canonical
closure-coefficient exchange for existentially supplied normalized lifts.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompletedChernNormalizedUnique": "49de4b2b0d9572870105f276c4db25b07a546321", "Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone": "9ffe1f004aa401e3aa9d5a1c5f6b6d65addd9e51", "Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNoneCanonical": "e6fcf5f8a5db30a619d8d07796d8ed26f254b1a1"}, "results": {}, "time": "2026-10-28T08:20:16+0800", "transitive": 0, "version": 1}
```

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
