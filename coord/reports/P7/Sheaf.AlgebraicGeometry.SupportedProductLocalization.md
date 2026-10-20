## What changed

Closed the distinguished-triangle conjuncts of
`AlgebraicGeometry.Etale.supportedProductLocalizationFirst` and
`AlgebraicGeometry.Etale.supportedProductLocalizationSecond`. The source triangles are
obtained by mapping normalized support triangles through tensor-right and tensor-left.
For the target triangles, the bounded-below external product is packaged as an object of
the canonical bounded-below derived subcategory and
`normalizedSupportTriangle_distinguished` is applied. The remaining component-extension
conjuncts are named as two lower-level public theorems in the same module, with matching
DAG nodes.

## Proved and sorry left

Proved the source and target distinguishedness conjuncts of
`supportedProductLocalizationFirst` and `supportedProductLocalizationSecond`, and retained
the existing proof of `supportedProductLocalization_naturality`.

The following named theorems remain as split-off holes:

- `supportedProductLocalizationFirst_map` —
  `lem-pur-supported-product-localization-first-map`.
- `supportedProductLocalizationSecond_map` —
  `lem-pur-supported-product-localization-second-map`.
- `supportedProductLocalization_openFirst` —
  `lem-pur-supported-product-localization`.
- `supportedProductLocalization_openSecond` —
  `lem-pur-supported-product-localization`.
- `supportedProductLocalization_openRows` —
  `lem-pur-supported-product-localization`.

## No longer needed

No imports or declared proof dependencies were pruned. The two new component-extension
nodes are now the explicit dependencies for the corresponding first and second localization
theorems.

## Where the brief, the DAG or earlier work was wrong

The original module statements use unbounded derived-category objects for the target
triangles while the available normalized-triangle theorem is stated for the bounded-below
subcategory. The explicit `_hF` bounded-below hypothesis supplies the missing packaging:
`externalProduct ... K.obj L.obj` is itself an object of `DerivedCategory.Plus`. This
conversion is required before applying `normalizedSupportTriangle_distinguished`.

## New nodes

`lem-pur-supported-product-localization-first-map` records the remaining first-variable
component-extension conjunct.

`lem-pur-supported-product-localization-second-map` records the remaining second-variable
component-extension conjunct.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
