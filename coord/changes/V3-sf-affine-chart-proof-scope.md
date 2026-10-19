# Sheaf.Paper.SfAffineChartFactorizationGluing proof notation scope

## Reason

The proved private helpers use the zero object in the derived and sheaf categories.
They need the scoped `ZeroObject` notation. The interface checker reports the added
command conservatively as an interface change. No public signature, definition,
instance, attribute or public import changes. All helper declarations are private
and fully proved. This is the held item of group V3.

## Old

```lean
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
```

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry
```

## Users

`tools/downstream.py Sheaf.Paper.SfAffineChartFactorizationGluing --uses
exists_sf_affine_chart_factorization_gluing` lists 180 downstream modules and finds
no use of the theorem outside its declaring module. An import search finds one
direct importer, listed below. All downstream statements keep the same meaning:
no mathematical object or predicate changes, and the theorem signature is unchanged.
The extra command opens notation only for this source file. No consumer adaptation
is required, and no target statement or definition used by a target changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfAffineChartFactorizationGluing | V3 | Assigned theorem proved; private helpers use zero-object notation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Direct importer; unchanged public interface, no adaptation. |

## Status

landed 20261019T034323-L-421063 2026-10-19 (merge of deliver/V3/Sheaf.Paper.SfAffineChartFactorizationGluing)
