# Sheaf.AlgebraicGeometry.AffinePolynomialLocalizedTorOfStalkwise

## Reason

Second reading removes an unused public import of the projective-dimension theory.
The localizedModule in the unchanged statement requires only ModuleCat.Localization.
No declaration signature, visibility, definition, or target meaning changes.

## Old

```lean
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
```

## New

```lean
public import Mathlib.Algebra.Category.ModuleCat.Localization
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffinePolynomialLocalizedFiniteProjectiveDimension | N3 (authorship; current claim not recorded locally) | No adaptation: it already publicly imports Mathlib.RingTheory.LocalProperties.ProjectiveDimension itself, preserving all symbols and instances removed from the item's exports. Its statement and proof are unchanged. |

This is the sole direct importer, found by searching both source roots. Because it
independently imports the removed module, its transitive users also retain that interface.
No definition changes and no target statement review is reopened. No forced adaptation.

## Status

landed 20261013T131327-L-4034618 2026-10-13 (merge of deliver/P4/Sheaf.AlgebraicGeometry.AffinePolynomialLocalizedTorOfStalkwise)
