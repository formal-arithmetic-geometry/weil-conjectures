# integralModel_locallyFree_flat and integralModel_flat_detect: proof import

## Reason

Restore the quarantined generator module after the 2026-10-22 upstream sync.
Its rework row identifies an overloaded comparison at archive line 501.
The comparison moved into a Sheaf.UpstreamExtra module when the adopted upstream
file was restored verbatim. Import that actual private home. This is a proof-import
repair; no proof body, definition, instance, public signature, or public import changes.

## Old

```lean
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

The four proof terms refer to `Mod.relativeTensorRightIso`.

## New

```lean
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

The four existing proof terms still refer to `Mod.relativeTensorRightIso`, now
resolved from the actual private declaration in the imported Sheaf.UpstreamExtra
module. Its type remains `Mod.tensorLeft M ≅ MonoidalCategory.tensorRight M`.

## Users

The changed lemmas are private. Direct importers of the restored module were
searched in both the live and quarantine trees; all seven are currently in
quarantine. They retain every public declaration they previously imported, and
none is edited. The normal downstream script reports the item as unknown because
its source is quarantined; the direct-import source search includes the archive.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing` | unclaimed | Public API unchanged; quarantined consumer retained. |
| `Sheaf.Paper.RationalLocalizedHom` | unclaimed | Public API unchanged; quarantined consumer retained. |
| `Sheaf.Paper.TamePairProperGenerators` | unclaimed | Public API unchanged; quarantined consumer retained. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Public API unchanged; quarantined consumer retained. |
| `Sheaf.Paper.GeometricCondensedFiniteScalarModel` | unclaimed | Public API unchanged; quarantined consumer retained. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Public API unchanged; quarantined consumer retained. |
| `Sheaf.SixFunctors.CommonFieldLatticeGenerators` | unclaimed | Public API unchanged; quarantined consumer retained. |

## Status

landed 20261022T113816-L-259974 2026-10-22 (merge of deliver/A4/Sheaf.SixFunctors.IntegralModelsGenerators)
