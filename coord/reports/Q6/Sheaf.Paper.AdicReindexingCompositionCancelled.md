## What changed

The cancelled composition theorem now combines two explicit proof stages: a finite integral-stage representative calculation and descent through rational localization and common-stage representatives. The item theorem itself is proved by applying these two intermediate declarations. The finite-stage proposition is defined in `AdicReindexingCompositionCancelledEquation`, with its calculation theorem in `AdicReindexingCompositionCancelledStage`; the descent theorem is in `AdicReindexingCompositionCancelledDescent`.

## Proved and sorry left

Proved:

- `normalized_reindexing_composition_cancelled`.

The following strictly smaller proof steps remain as named intermediate theorems:

- `normalized_reindexing_composition_cancelled_stage` in `AdicReindexingCompositionCancelledStage` (finite integral-stage calculation).
- `normalized_reindexing_composition_cancelled_descent` in `AdicReindexingCompositionCancelledDescent` (localization and common-stage descent).

The proposition definition `normalized_reindexing_composition_cancelled_equation` has no proof hole.

## No longer needed

None. The finite-stage module imports the three declared proof dependencies from the original DAG route; the item uses the stage and descent modules, and the descent module imports the stage module.

## Where the brief, the DAG or earlier work was wrong

The original single proof step combines two independent arguments: the finite integral representative calculation and the subsequent common-stage descent. The delivery records them as separate strictly smaller statements so that the parent theorem has a real combining proof and each unresolved calculation has a precise handoff.

## New nodes

- `def-sf-adic-reindexing-functoriality-comp-cancelled-equation`
- `lem-sf-adic-reindexing-functoriality-comp-cancelled-stage`
- `lem-sf-adic-reindexing-functoriality-comp-cancelled-descent`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingCompositionCancelled": "23599869d716fdfffa737a59ca6a62e144645916", "Sheaf.Paper.AdicReindexingCompositionCancelledDescent": "bb8e9fb87434e11793a50b8df48375d88b0f04d0", "Sheaf.Paper.AdicReindexingCompositionCancelledEquation": "44669ec5ff4221ad1d88487dc2f99e9040fb0d6c", "Sheaf.Paper.AdicReindexingCompositionCancelledStage": "12752c619e7a0174bd80f9b14acb7095f4bbf50a"}, "results": {"Sheaf.Paper.AdicReindexingComposition": {"hash": "f31e857ae4f4436ec86e59175ac78bfdf2e06648", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T08:15:12+0800", "transitive": 0, "version": 1}
```

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
