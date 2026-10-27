# AlgebraicGeometry.ProEtale.IntegralFiniteScalar.integralFiniteScalarPerfectModel

## Reason

Add two strictly simpler public obligations: the normalized derived comparison, excluding projection/gamma invertibility, and finite-cone projection invertibility, independent of the quotient and arithmetic. The parent combines these with proved arithmetic and a proved derived restriction conservativity/cancellation argument.

## Old

```lean
(no declarations for the two independent steps)
```

## New

```lean
derivedAssertions_of_finite_integral_resolution and finiteFreeScalarProjection, each with its own node, both in the new module Sheaf.Paper.FiniteFreeScalarDerivedComparison. (Reviewer fix: the delivered finiteFreeScalarProjection had overwritten the existing K8 module Sheaf.Paper.FiniteFreeScalarProjection, deleting WeilConjectures.FiniteFreeProjectionExchange.finite_free_scalar_projection of node lem-pur-finite-free-scalar-projection, used by Sheaf.Paper.FiniteFreeProjectionExchange; that module is restored unchanged.)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralFiniteScalarPerfectModel | R2 | Publicly reexports the unchanged interface and assembles the independent steps. |

No current downstream Lean importers (tools/downstream.py); target statements and all original declaration signatures and bodies are preserved. DAG parents retain the original item node; they continue to refer to the same theorem. The new definitions module is not a replacement for the theorem.

## Status

landed 20261025T202921-L-2766219 2026-10-25 (merge of deliver/R2/Sheaf.Paper.IntegralFiniteScalarPerfectModel)
