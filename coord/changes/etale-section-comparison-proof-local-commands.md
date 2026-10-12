# AlgebraicGeometry.Etale.etaleSectionShortComplex_pullback_comparison

## Reason

The proof uses fibre-product and biproduct notation and the standard local instance
which derives preservation of binary biproducts from preservation of finite biproducts.
The static interface detector conservatively classifies additions to open/attribute
commands as an interface change, so this record documents their actual effect.
The declaration signature and public imports are unchanged. The new private helpers
are fully proved; they occur only in proofs, not in any public definition or signature.

## Old

```lean
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale
```

The public theorem signature is unchanged from its original recorded Lean statement
in lem-weil-pbc-etale-mayer-vietoris-section-comparison.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
```

The open commands affect lexical name resolution only. The local instance attribute
ends with the namespace and is not exported. Declaration-local transparency options
permit the proof to use the concrete section-complex definitions; they alter neither
the statements nor the data of those definitions. No consumer needs adaptation.
The two new modules have new node records and contain no altered existing API.

## Users

A source-name search finds only the assigned module and the following external user.
The supplied downstream.py --uses command was also run. No theorem type, universe,
or definition used by any target changes; target semantic review is not reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionDiagram | unclaimed | The theorem has the identical signature; the existing call needs no change. |

The generic interface command marker has no external textual users. The additional
open/attribute commands do not export names, instances, or notation to consumers.

## Status

landed 20261012T144055-L-2089643 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.EtaleMayerVietorisSectionComparison)
