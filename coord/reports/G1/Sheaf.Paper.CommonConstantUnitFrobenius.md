## What changed

Added the rational-stage split module `Sheaf.Paper.RationalConstantUnitFrobenius`.
It records the finite coefficient stage of the normalized constant-unit Frobenius
calculation and is imported by the assigned module. The assigned common-stage
statement remains open. Updated its DAG proof route to pass through the split node.

## Proved and sorry left

No existing sorry was closed. The assigned declaration
`WeilConjectures.ConstantPurityFrobenius.commonUnit_frobenius` remains `sorry`.
The new declaration `WeilConjectures.ConstantPurityFrobenius.rationalizedUnit_frobenius`
is a named split-off theorem and remains `sorry` at node
`lem-pur-common-constant-unit-frobenius-rational`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The current global build records a bad import for `Sheaf.Paper.FrobeniusGeometricExchange`,
but the module is present and compiles in the sandbox. No statement was changed.

## New nodes

`lem-pur-common-constant-unit-frobenius-rational` records the strictly lower rational
coefficient stage needed before applying the common-stage inclusion.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonConstantUnitFrobenius": "b0f6056e9fbb47b15c114251b1f18936005c8afb", "Sheaf.Paper.RationalConstantUnitFrobenius": "b9c12688ef4f50ece6617604335dbb668172b864"}, "results": {}, "time": "2026-10-28T07:12:00+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
