## What changed

Repaired the module's public import by replacing the unavailable
`Sheaf.Paper.EtaleBrownProjectionRealization` import with
`Sheaf.Paper.StrictEtaleSystemInterfaces`. Added the explicit mate-pasting
remainder module `Sheaf.Paper.EtaleBrownOpenSingletonEvaluationCore`, and reduced
the item theorem to that expansion.

## Proved and sorry left

No original theorem hole was closed. The item theorem
`AlgebraicGeometry.etaleBrownOpenSingletonEvaluation` remains a sorry. The
strictly simpler split theorem
`AlgebraicGeometry.etaleBrownOpenSingletonEvaluationCore` is also left as a named
sorry for the next worker.

## No longer needed

`Sheaf.Paper.EtaleBrownProjectionRealization` is no longer imported; the statement
uses only the strict étale system interfaces and their derived scalar/evaluation
fields.

## Where the brief, the DAG or earlier work was wrong

The global build record reported a bad import of
`Sheaf.Paper.EtaleBrownProjectionRealization`. The corrected import compiles the
item and its direct importer. The remaining proof is the explicit scalar/open mate
pasting step recorded in the new node.

## New nodes

`lem-pur-etale-brown-open-singleton-evaluation-core` records the expanded mate
pasting remainder in `EtaleBrownOpenSingletonEvaluationCore.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleBrownOpenSingletonEvaluation": "01fa75262e25396654d88ab3ef8e270d73e00641", "Sheaf.Paper.EtaleBrownOpenSingletonEvaluationCore": "e2977f480e1f3458b91e0f969566c2ce7637df36"}, "results": {"Sheaf.Paper.EtaleBrownGeometricComparisons": {"hash": "25963ce8089e94e3831cf1beade33a99f1ea4963", "status": "SLOW"}}, "seconds": 67, "time": "2026-10-28T04:00:13+0800", "transitive": 0, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
