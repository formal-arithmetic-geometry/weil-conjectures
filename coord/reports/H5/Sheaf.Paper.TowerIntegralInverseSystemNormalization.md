## What changed

Added `TowerIntegralAbelianComparison` and `TowerIntegralUnitNormalization` as the two
strictly smaller proof obligations from the blueprint plan. The item theorem now obtains
the abelian comparison and the normalized coefficient-unit comparison and combines them
with a real existential-elimination proof. Added the corresponding DAG nodes and updated
the item node's proof route and proof dependencies.

## Proved and sorry left

The item declaration `integralInverseSystem_normalization` is proved by combining the two
smaller statements. Two sorries remain, one in each split-off declaration:

- `integralInverseSystem_abelian_comparison` in
  `lem-sp-tower-integral-abelian-comparison`;
- `integralInverseSystem_unit_normalization` in
  `lem-sp-tower-integral-unit-normalization`.

No definitions contain sorry.

## No longer needed

None. The original imports remain necessary for the item statement and for the two
split-off proof obligations; no DAG dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original two-step proof plan did not expose separate Lean declarations for the
abelian assembly and the coefficient-unit normalization. The delivery makes those two
strictly smaller obligations explicit; the target statement and all existing signatures
are unchanged.

## New nodes

`lem-sp-tower-integral-abelian-comparison` records the abelian tower assembly obligation.
`lem-sp-tower-integral-unit-normalization` records the coefficient-unit and integer
normalization obligation conditioned on the assembled abelian isomorphism.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerIntegralAbelianComparison": "775f9bbff5c2776c0f6301ace7cb3abac831df05", "Sheaf.Paper.TowerIntegralInverseSystemNormalization": "9fa9e6ac55a49e1909864da17dc81c22d7d7228d", "Sheaf.Paper.TowerIntegralUnitNormalization": "9ec02394ad080f0dc4637f8081c58692797b271a"}, "results": {}, "time": "2026-10-28T03:41:33+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
