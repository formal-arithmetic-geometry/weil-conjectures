## What changed

Replaced the upper theorem proof with a complete existential-elimination proof. Added two public intermediate theorem modules: `ExceptionalProperOpenOriginConstruction`, which states the existence of the strict pro-etale support and comparison data, and `ExceptionalProperOpenOriginProperties`, which states the bounded-origin, invertibility, bound, and evaluation properties for supplied data. The parent imports both modules and combines their conclusions.

## Proved and sorry left

The parent declaration `AlgebraicGeometry.exceptionalProperOpenOriginComparison` is proved. The two strictly simpler intermediate declarations remain `sorry`: `AlgebraicGeometry.exceptionalProperOpenOriginConstruction` and `AlgebraicGeometry.exceptionalProperOpenOriginProperties`. These are recorded by nodes `lem-sf-exceptional-proper-open-origin-construction` and `lem-sf-exceptional-proper-open-origin-properties`.

## No longer needed

No imports from the original interface module were removed. The parent proof uses only the two new intermediate modules; the original geometric proof dependencies are retained as the stated sources of those intermediate nodes.

## Where the brief, the DAG or earlier work was wrong

The original item bundled construction of the pro-etale support/comparison data with all bounded-origin and evaluation properties in one theorem. This was too coarse to prove directly. Splitting those genuinely distinct stages yields a compiling parent proof while preserving the full target statement.

## New nodes

`lem-sf-exceptional-proper-open-origin-construction` is stated in `lean/Sheaf/Paper/ExceptionalProperOpenOriginConstruction.lean` and records the construction stage.

`lem-sf-exceptional-proper-open-origin-properties` is stated in `lean/Sheaf/Paper/ExceptionalProperOpenOriginProperties.lean` and records the bounded-origin and evaluation stage.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalProperOpenOriginComparison": "5ee6bf5844a3e5298ff6655659aa5212bc25d760", "Sheaf.Paper.ExceptionalProperOpenOriginConstruction": "063ec5ac2ec6f01b19af2a39b1b84e61790ee964", "Sheaf.Paper.ExceptionalProperOpenOriginProperties": "c5a5e34952c1d7e47f1a2d4a40542d651f673618"}, "results": {}, "time": "2026-10-28T00:53:24+0800", "transitive": 0, "version": 1}
```

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
