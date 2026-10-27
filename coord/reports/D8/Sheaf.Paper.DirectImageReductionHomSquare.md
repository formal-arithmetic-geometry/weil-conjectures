## What changed

Filled three previously unfinished proofs in `Sheaf.Paper.DirectImageReductionHomSquare`.
`geometricPull_additive` proves additivity by the sectionwise additive direct image and the
ordinary pullback/pushforward adjunction. `completedPull_colimits` and
`finitePull_colimits` use the corresponding ordinary adjunctions and Mathlib's theorem that
left adjoints preserve finite colimits. The module compiles cleanly.

## Proved and sorry left

Proved (3 holes closed): `geometricPull_additive`, `completedPull_colimits`, and
`finitePull_colimits`.

Seven documented holes remain in the item: `completedPull_limits`, `finitePull_limits`,
`geometricAdjunction_existsUnique`, `tensorPull_existsUnique`, `hom_square`,
`transition_representation`, and `hom_square_transitions`.

## No longer needed

None. All existing imports and the reviewed DAG route remain needed for the unfinished
normalization and transition results.

## Where the brief, the DAG or earlier work was wrong

Nothing identified. The remaining statements and their proof plan are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DirectImageReductionHomSquare": "06f52082c7152f924b3c76bcc0f82ce1738a4fc6"}, "results": {}, "time": "2026-10-28T06:49:47+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
