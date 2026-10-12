# reduced_product_localization

## Reason

Narrow the public tensor-product dependency to the module that supplies the
unchanged statement's tensor algebra structures. `TensorProduct.Maps` is used
only in the new proof and is available through plain proof imports.
No declaration statement or definition changes. This record documents the
public-import change requested by the stage-3 preflight.

## Old

```lean
public import Mathlib.RingTheory.TensorProduct.Maps
```

## New

```lean
public import Mathlib.RingTheory.TensorProduct.Basic
```

The proof has plain imports of `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.RingTheory.Localization.Ideal`, `Mathlib.RingTheory.TensorProduct.Quotient`,
and `Mathlib.RingTheory.TensorProduct.Pi`. The latter supplies `Maps` privately.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ReducedProductLocalization --uses
reduced_product_localization` reports 138 downstream modules but only the item
and the following direct user mention this declaration. The sole direct importer
already publicly imports `Mathlib.RingTheory.TensorProduct.Maps` itself, so all
its statements and downstream public dependencies retain access to `Maps`.
The import of this item in that user is plain. No downstream statement, definition,
or proof needs adaptation; target meanings are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ReducedProductLocalization | C3 | Statement byte for byte unchanged; proof complete; public import narrowed. |
| Sheaf.AlgebraicGeometry.RefineFiniteDomainSplitting | unclaimed in the local claim snapshot | No change; independently imports Maps publicly; compiled unchanged against the delivered module in a scratch validation set. |

No adapted modules are delivered. No target statement or target-used definition
changes, so target statement review is not reopened.

## Status

landed 20261012T173814-L-3292215 2026-10-12 (merge of deliver/C3/Sheaf.AlgebraicGeometry.ReducedProductLocalization)
