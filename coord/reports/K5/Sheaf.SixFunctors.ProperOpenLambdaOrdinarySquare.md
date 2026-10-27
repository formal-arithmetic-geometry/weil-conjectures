## What changed

Added `Sheaf.SixFunctors.ProperOpenLambdaFourFactorSquare`, which states the
strictly smaller four-factor component square with an arbitrary child comparison.
The assigned module imports it and proves `properOpenLambdaOrdinarySquare` by
substituting `properOpenOrdinaryR` for that child comparison and unfolding the
recursive source and target maps. The component theorem remains a named split
statement with its documented proof route.

## Proved and sorry left

`properOpenLambdaOrdinarySquare` is proved. The split theorem
`properOpenLambdaFourFactorSquare` remains `sorry`, with node
`lem-sf-proper-open-lambda-four-factor-square`.

## No longer needed

None. The assigned module still needs its original `OpenInterchangeReductionData`
import and the new component-square import.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the component square needed to connect the
independently defined system and ringed four-factor lambda maps. The new node
records that missing strictly smaller step.

## New nodes

`lem-sf-proper-open-lambda-four-factor-square` is declared in
`lean/Sheaf/SixFunctors/ProperOpenLambdaFourFactorSquare.lean`; its DAG node is
`dag/nodes/sec-six-functors/lem-sf-proper-open-lambda-four-factor-square.json`.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.SixFunctors.ProperOpenLambdaFourFactorSquare": "42f737c0f99ca48240ef07c8eafbceb3b3fc24b3", "Sheaf.SixFunctors.ProperOpenLambdaOrdinarySquare": "7cfdaa00efe98d9896d6381d75760699885ba5ea"}, "results": {"Sheaf.SixFunctors.ProperOpenLambdaCompletionIso": {"hash": "2829c260831c134f269dcef841c88b31a984192a", "status": "OK"}, "Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport": {"hash": "99cd2303ea857270c57478bdca4038e935ed43aa", "status": "OK"}, "Sheaf.SixFunctors.ProperOpenLambdaReductionSquare": {"hash": "f322e69491fd3f45c4e9dac73841eeb0b3d2034d", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T03:46:27+0800", "transitive": 0, "version": 1}
```

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
