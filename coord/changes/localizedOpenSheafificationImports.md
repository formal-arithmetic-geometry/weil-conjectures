# localizedOpenSheafificationImports

## Reason

The sheafification transport proof uses no tensor product or monoidal structure.
Remove the unused public import of the module-sheaf monoidal construction.
The existing public pushforward monoidal import is retained: the direct user
LocalizedOpenTensorEquivalence uses its instance for presheaf transport.
No definition or theorem signature changes, and no module needs adaptation.

## Old

```lean
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
```

## New

The above import is removed. Add the proof-only import:

```lean
import Mathlib.CategoryTheory.Adjunction.Restrict
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LocalizedOpenSheafification | J1 | Proved with unchanged signature; no monoidal argument. |
| Sheaf.AlgebraicGeometry.LocalizedOpenTensorEquivalence | unclaimed | Already publicly imports the removed module directly; no adaptation. |

The sole direct importer imports the removed module itself, so all further
importers continue to reach it through their existing routes. The targets and
the definitions used in their statements are unchanged.

## Status

landed 20261013T143546-L-560787 2026-10-13 (merge of deliver/J1/Sheaf.AlgebraicGeometry.LocalizedOpenSheafification)
