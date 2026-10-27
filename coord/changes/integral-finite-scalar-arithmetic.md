# AlgebraicGeometry.ProEtale.IntegralFiniteScalar.PerfectModelArithmetic

## Reason

Add the arithmetic prefix as a separate proposition, and prove it from the existing finite_integral_condensed_resolution. The rank-zero clause is handled explicitly. No target or existing signature changes.

## Old

```lean
(no declaration)
```

## New

```lean
PerfectModelArithmetic is the arithmetic and short-exact prefix of PerfectModel; perfectModelArithmetic_of_finite_integral proves it.
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralFiniteScalarPerfectModel | R2 | Publicly reexports the unchanged interface and assembles the independent steps. |

No current downstream Lean importers (tools/downstream.py); target statements and all original declaration signatures and bodies are preserved. DAG parents retain the original item node; they continue to refer to the same theorem. The new definitions module is not a replacement for the theorem.

## Status

landed 20261025T202921-L-2766219 2026-10-25 (merge of deliver/R2/Sheaf.Paper.IntegralFiniteScalarPerfectModel)
