# Etale.sheaf_clopen_product imports

## Reason

The proof requires product limits, local sheaf isomorphisms, and open immersion lemmas.

## Old

`import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`

## New

`import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`
`import Mathlib.CategoryTheory.Sites.Limits`
`import Mathlib.CategoryTheory.Sites.LocalProperties`
`import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement`
`import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct | Y3 | proof imports updated |

## Status

landed 20261012T144202-L-2113534 2026-10-12 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct)
