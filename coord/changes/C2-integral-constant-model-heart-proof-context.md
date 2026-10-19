# Sheaf.Paper.IntegralConstantModelHeart proof context

## Reason

The original hole is replaced by private coefficient-transport, zero-object,
cohomology, and smallness proofs. The static interface check records their added
section, universe, scope and namespace commands. These provide local proof context;
the public theorem signature, coefficient definition and public imports are unchanged.

## Old

The original module had only the following context after its public section:

```lean
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
```

It declared the coefficient abbreviation unchanged, followed by the theorem
`AlgebraicGeometry.ProEtale.integralConstantModelHeart` with proof `by sorry`.

## New

The coefficient abbreviation and theorem signature are unchanged. Between them,
private proved helpers use the following additional context inside local sections:

```lean
section Helpers
open MonoidalCategory MonObj CondensedRing
open scoped CategoryTheory.Obj
open scoped ZeroObject
universe v₁ v₂ u₁ u₂
```

Additional local sections delimit presentation, general coefficient and Serre
transport arguments; they close before the public theorem. No public instance,
notation or definition is added to this module. Proof imports are private.

## Users

`tools/downstream.py` reports one downstream module. Its original source uses the
unchanged coefficient abbreviation; the theorem statement and coefficient data keep
exactly their previous meanings. No target or consumer signature changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralConstantModelHeart | C2 | Private proofs and local proof context added; public signatures and data unchanged. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Same coefficient abbreviation and theorem statement; no source adaptation. |

## Status

landed 20261019T093304-L-2289498 2026-10-19 (merge of deliver/C2/Sheaf.Paper.IntegralConstantModelHeart)
