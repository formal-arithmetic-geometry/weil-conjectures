# EtaleAwayOfLocalizedCotangentVanishing import visibility

## Reason

Mathlib.RingTheory.Etale.Locus supplies only proof lemmas. The signature compiles with
that module imported privately; the retained public morphism Etale module supplies the
signature vocabulary. No statement, definition, or target meaning changes.

## Old

```lean
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
```

## New

```lean
import Mathlib.RingTheory.Etale.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
```

## Users

Read both direct importers, found by tools/downstream.py --direct. Both import the item
privately, so its removed re-export was already unavailable to their public users.
The smooth-section importer uses no locus declaration in its proof or signature;
the other direct importer has its own public Etale.Locus import. No adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion | not consulted (no adaptation) | independently publicly imports Etale.Locus; unchanged |
| Sheaf.Paper.SmoothSectionEtaleLift | not consulted (no adaptation) | imports this item only privately; uses no locus declaration; unchanged |

## Status

landed 20261012T095908-L-318610 2026-10-12 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing)
