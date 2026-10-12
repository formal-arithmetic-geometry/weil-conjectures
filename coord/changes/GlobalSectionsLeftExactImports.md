# AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor_additive_leftExact (imports)

## Reason

Remove the unused public import of LeftExact. The retained Modules.Sheaf import
already exposes every name needed by the unchanged signatures and proof. A scratch
copy without LeftExact compiles and has only the three permitted axioms. This is
an import cleanup, with no definition or statement change and no target meaning
change. Both direct users import GlobalSectionsLeftExact privately and do not use
any declaration exclusive to LeftExact.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.LeftExact
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact | R2 | Unused public import removed; signatures and definition unchanged; proof compiles. |
| Sheaf.Paper.PQFCohomology | none (no adaptation) | Private importer; signatures use independently imported ringed-space cohomology; no LeftExact-only declaration used. |
| Sheaf.AlgebraicGeometry.LeraySpectralSequence | none (no adaptation) | Private importer; signatures use independently imported spectral-sequence declarations; no LeftExact-only declaration used. |

## Status

landed 20261012T063518-L-3159141 2026-10-12 (merge of deliver/R2/Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact)
