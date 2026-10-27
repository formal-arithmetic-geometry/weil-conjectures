## What changed

The main theorem `integralScalarIsomorphismExchange` now combines the already isolated integral
clause with two strictly smaller named clauses: the finite-level equality and the normalized
strict total-limit equation. Both new clauses are documented and represented by DAG nodes. The
Lean module still imports only its original proof dependencies.

## Proved and sorry left

The `integralScalarIsomorphismExchange` hole was closed by a real conjunction proof, reducing it
to the two strictly smaller statements below and the existing integral clause. Two holes were
split off as named theorems: `finiteScalarIsomorphismExchange` and
`strictLimitEquation_of_integralScalarIsomorphismExchange`. The remaining holes are
`openInverse_isIso`, `integralScalarIsomorphismExchange_integral`, `scalarPull_finiteTor`,
`rectangle_refinement`, and `Systems.strictScalarIsomorphismExchange`.

## No longer needed

None. No imports or existing DAG dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan presented the finite-system and normalized-limit arguments as portions of
one very large theorem. In this Lean module they are separate conclusions and cannot be proved by
conjunction construction without naming their independent proof obligations. The delivery records
them as two strictly smaller split statements while preserving the parent statement and route.

## New nodes

- `lem-pur-integral-scalar-isomorphism-exchange-finite-level`
- `lem-pur-integral-scalar-isomorphism-exchange-strict-limit`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralScalarIsomorphismExchange": "26569d7f51a35db777d0e48abd8ba0e2836b8ab2"}, "results": {"Sheaf.Paper.ZlFrameworkOpenExchange": {"hash": "817d737b9ee39d4db3caf4e5d27ae2865eee2c92", "status": "OK"}}, "seconds": 39, "time": "2026-10-28T07:13:37+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
