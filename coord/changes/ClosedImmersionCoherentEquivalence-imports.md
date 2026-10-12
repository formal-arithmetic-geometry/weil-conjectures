# ClosedImmersionCoherentEquivalence proof imports

## Reason

The proof uses `open MonoidalCategory Scheme.Modules` and imports the tensor-section API for the
private ideal-product helper.

## Old

The module had no proof-only import of `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`
and no corresponding namespace openings.

## New

The module imports `WeilConjectures.AlgebraicGeometry.Modules.TensorSection` and opens the namespaces
needed by the private helper.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence | F2 | proof elaboration only |

## Status

landed 20261012T173823-L-3294699 2026-10-12 (merge of deliver/F2/Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence)
