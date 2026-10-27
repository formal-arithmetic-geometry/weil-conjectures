## What changed

Repaired the stale module import and replaced the proper/open interchange hole by a
composition of two named proof steps. Added `ProperOpenLambdaReductionSquareUnbounded`
for the four-factor lambda square and `ProperOpenInterchangeFromLambda` for the
open-adjunction transpose and open-counit pasting.

## Proved and sorry left

The original declaration `properOpenInterchangeReductionSquare` is proved from the
two split-off declarations. Two strictly simpler declarations remain `sorry`:
`properOpenLambdaReductionSquare_unbounded` (the four-factor lambda square) and
`properOpenInterchange_from_lambda_square` (the final transpose step).

## No longer needed

No proof imports were removed. The stale dependency on the absent
`Sheaf.SixFunctors.OpenInterchangeReductionData` is restored from the current
library source; the item's public interface is unchanged.

## Where the brief, the DAG or earlier work was wrong

The current build error was caused by an obsolete bad-import record after the
restored dependency was moved back into the library. The existing bounded lambda
statement does not apply here because the interchange statement bounds the two
interchange endpoints, while the additional lambda source word has no endpoint
length bound. The unbounded lambda step records this distinction explicitly.

## New nodes

`lem-sf-proper-open-lambda-reduction-square-unbounded` records the four-factor lambda
calculation with the interchange endpoint bounds.

`lem-sf-proper-open-interchange-from-lambda` records the transpose of the inverse
lambda square under the open adjunction and pasting with the open counit.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.ProperOpenInterchangeFromLambda": "1646081a46053d3410fec302492273eb21037a4e", "Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare": "f597d6adce2c1e73c282dafa452f4f779a953d7f", "Sheaf.SixFunctors.ProperOpenLambdaReductionSquareUnbounded": "0d2e5dfec598e66b6a968b3a9c8aaae51a6722dc"}, "results": {}, "time": "2026-10-28T00:58:57+0800", "transitive": 0, "version": 1}
```

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
