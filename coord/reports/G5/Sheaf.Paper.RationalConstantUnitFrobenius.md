## What changed

Added `Sheaf.Paper.IntegralConstantUnitFrobenius`, defining the canonical integral square component and recording the completed integral normalized-unit Frobenius square as a strictly smaller proof obligation. The target module imports this helper privately for proof development but retains its original target statement.

## Proved and sorry left

The target declaration `rationalizedUnit_frobenius` remains `sorry`. The new lower declaration `integralUnit_frobenius` also remains `sorry` with node `lem-pur-common-constant-unit-frobenius-integral`; it is the completed integral-stage square, strictly below the rational target.

## No longer needed

No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

Direct unfolding of the rational pullback and localization definitions exceeds the heartbeat budget. The rational proof requires the integral normalized-unit square before scalar localization; that smaller step is now stated explicitly.

## New nodes

`lem-pur-common-constant-unit-frobenius-integral` records the completed integral normalized-unit Frobenius square in `Sheaf.Paper.IntegralConstantUnitFrobenius`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralConstantUnitFrobenius": "cc89211672d1ac6acd92c5f919d71bc3e1d73096", "Sheaf.Paper.RationalConstantUnitFrobenius": "b08713168d8755e069980d389888c79debfcc4d3"}, "results": {}, "time": "2026-10-28T08:17:26+0800", "transitive": 0, "version": 1}
```

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
