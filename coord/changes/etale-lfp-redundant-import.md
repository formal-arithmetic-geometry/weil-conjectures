# Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType imports

## Reason

Remove a redundant direct public import. The remaining public import of
`Mathlib.AlgebraicGeometry.Morphisms.Etale` already publicly imports `Smooth`,
which publicly imports `FinitePresentation`, which publicly imports
`QuasiSeparated`, which publicly imports `QuasiCompact`. Thus exactly the same
Mathlib declarations and instances remain visible to every importer. No theorem
signature, definition, notation, or target meaning changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType --uses
etale_lfp_and_finiteType_over_field QuasiCompact` reports 178 transitive importers;
none mentions the theorem. The two direct importers are below. For every
transitive importer, the complete public re-export path above preserves the same
QuasiCompact declarations and instances, so there is no statement effect or
required adaptation. No downstream module is delivered or edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedPointSheafApproximation | unclaimed | Same public imports transitively; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportDimensionUnion | unclaimed | Same public imports transitively; no adaptation. |

The module compiles without the redundant import. The independent axiom probe
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261017T041408-L-2535697 2026-10-17 (merge of deliver/F4/Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType)
