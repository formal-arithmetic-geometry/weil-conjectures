## What changed

Restored the delivered `Sheaf.SixFunctors.IntegralNormalizedFamily` proof into the
rework packet and adapted its limit conversion to the current dependency interface.
The private `selectDiagonalLimit` helper now unfolds
`DiagonalCompletedLimitSpec`, `DiagonalTrace.IsDiagonalLimit`,
`FiniteCartierNormalization`, `FiniteRootNormalization`, and `finiteCartierClass`
before applying the generic existential rearrangement. This preserves the complete
compatibility witness and makes the resulting proof typecheck against the current
`DiagonalTowerCoefficients` interface. The public `IntegralFamilyReference`
definition and `integralNormalizedFamily_exists` statement are unchanged.

## Proved and sorry left

The assigned module has zero `sorry` holes. The complete proof of
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralNormalizedFamily_exists`
is restored and repaired. Closed 0 of 0 holes; added 0 holes; split off 0 statements.

## No longer needed

No import, declaration, DAG dependency, or module is pruned. The direct imports
`Sheaf.Paper.DiagonalCoefficientReference` and
`Sheaf.Paper.DiagonalTowerCoefficients` remain necessary. The earlier continuation
based private helper and duplicate compatibility converter remain removed; the
explicit unfolding is required by the current irreducible normalization definitions.

## Where the brief, the DAG or earlier work was wrong

The previous delivery was removed from `lean/` when the global build found that a
new `DiagonalTrace.IsDiagonalLimit` interface no longer accepted the raw
finite-cycle presentation definitionally. The quarantined source records the exact
failure at the `diagonalTower_coefficients` call and the root fix: unfold the four
normalization names before passing `hlimit`. The retained delivered proof instead
performs that conversion in `selectDiagonalLimit`; unfolding
`DiagonalCompletedLimitSpec` there is also necessary because its type is a separate
wrapper around the expanded existential. This repair changes only proof terms and
DAG proof metadata; public statements, definitions, and imports are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralNormalizedFamily": "59b49eb6204f64d63c017d27800ae6aca3cb1d14"}, "results": {}, "time": "2026-10-28T09:14:44+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
