# Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions imports

## Reason

The second reading removes an unused direct public import. TensorSection already
provides the monoidal tensor structure and pure tensor sections; none of TensorProduct's
additional change-of-rings or tensor-power declarations occurs in this module's statement
or proof. The revised module compiles and its two declarations use only standard axioms.
No declaration signature, visibility or definition changes.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
```

## New

The above import is removed. The existing public imports of CommAlgebraSheaf and
TensorSection remain.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsCore | unclaimed in the local claims | Sole direct importer, by a plain proof-only import. Already publicly imports TensorProduct itself (line 9); every declaration and proof retains the same available imports. No adaptation required. |

Searched both plain and public imports throughout lean/. The item has no public importer;
its only direct importer explicitly retains the removed dependency. No downstream
statement, definition or proof becomes weaker, stronger or different.

## Status

landed 20261013T082347-L-1636594 2026-10-13 (merge of deliver/G4/Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions)
