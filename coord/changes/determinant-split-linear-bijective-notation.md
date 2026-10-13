# determinant_split_linear_maps_locally_bijective

## Reason

The static interface checker flags the new namespace-local command
`open scoped TensorProduct`. It enables tensor notation used in private algebraic helper
signatures and the theorem proof. It changes no declaration signature, instance, attribute,
notation definition or exported constant; opening a scoped notation does not open it for
importers. This record documents the command the checker conservatively classifies.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
```

The existing theorem signature is verbatim unchanged. All other additions in this module
are private helpers or proof-only imports. The new chart theorem is in a separate new module,
imported only for this proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | No change to signatures or notation available to importers; no adaptation. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal | unclaimed | No change to signatures or notation available to importers; no adaptation. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective | Y3 | Namespace-local tensor notation for private helper and proof. |

These are the three modules listed under declaration uses by tools/downstream.py.
All transitive importers retain the same public theorem interface. No target definition or
statement changes and no adaptation is forced.

## Status

landed 20261013T100230-L-2505776 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective)
