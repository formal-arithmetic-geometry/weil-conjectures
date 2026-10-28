## What changed

Proved `WeilConjectures.ConstantPurityFrobenius.rationalizedUnit_frobenius` in
`Sheaf.Paper.RationalConstantUnitFrobenius` by rationalizing the existing integral
Frobenius square. Private proved helpers identify pullback objects and maps, inverse
compositors, and equality transports with their localized integral counterparts.
The existing statements, public definitions and imports are unchanged.
The item's DAG proof now records this route.

Validation: the required remote single-file compiler passed without errors or
warnings in 15.4 seconds, including its private overlay of the current integral
dependency. Both existing declaration signatures were checked unchanged.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.ConstantPurityFrobenius.rationalizedUnit_frobenius`
(node `lem-pur-common-constant-unit-frobenius-rational`).
No holes remain in the item. No holes were added and no statements were split off.
The proof uses the existing named integral theorem `integralUnit_frobenius`;
this delivery makes no claim to close that dependency's hole.

## No longer needed

No imports or modules removed. No new finite-quotient or Roos-tower proof is needed
in this item: those calculations are encapsulated by the existing dependency
`lem-pur-common-constant-unit-frobenius-integral`.
`lem-pur-proetale-constant-ring-composition` and
`lem-pur-completed-operation-tower-substitution` are no longer direct proof
requirements of the rational node. The former remains an integral-node dependency;
this delivery does not withdraw either node or its module.

## Where the brief, the DAG or earlier work was wrong

The rational node's previous proof described finite quotient and completed tower
work even though that work is already isolated in the existing integral-square
node. Its final localization step can be proved from that integral theorem and
the existing normalized rational pullback/compositor specifications, without
another decomposition or any interface change.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalConstantUnitFrobenius": "265efe26a704e6b0ded21a67b3fe784511eb29f6"}, "results": {"Sheaf.Paper.CommonConstantUnitFrobenius": {"hash": "3e24bc10013089f3622934ae5565cdfaabe43f79", "status": "OK"}}, "seconds": 128, "time": "2026-10-28T10:32:12+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
