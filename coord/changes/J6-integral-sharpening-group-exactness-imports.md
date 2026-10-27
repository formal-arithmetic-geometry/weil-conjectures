# AlgebraicGeometry.FineFan.integral_sharpening_group_exactness imports

## Reason

The theorem is entirely about commutative monoids, Associates and group completion.
Its geometric imports bring in fine fans and log geometry that neither its
statement nor its complete proof uses. Replace them by the direct Mathlib API.
No existing public declaration, definition, attribute or instance changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
```

## New

```lean
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
```

The theorem signature is verbatim unchanged. The new helpers are private and proved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.GroupTheory.IntegralSharpeningGroupExactness | J6 | Complete proof; direct Mathlib imports |

`tools/downstream.py Sheaf.GroupTheory.IntegralSharpeningGroupExactness
--uses integral_sharpening_group_exactness` reports zero downstream modules; the
only textual use of the theorem is its declaration. An exact import-line search
also finds no direct importers. The DAG parents keep this theorem and all its
unchanged clauses available. No other module needs adaptation.

## Status

landed 20261026T082314-L-2160514 2026-10-26 (merge of deliver/J6/Sheaf.GroupTheory.IntegralSharpeningGroupExactness)
