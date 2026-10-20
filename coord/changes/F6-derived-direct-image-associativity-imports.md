# DerivedDirectImageCompositionAssociativity statement imports

## Reason

Restore the quarantined module with imports visible to its public statement. The
quarantine diagnostic reports that `Scheme` is imported privately. Its other public
signature ingredients also come from SchemeDerivedDirectImage. That module already
publicly imports DerivedCategory, so the separate DerivedCategory import is redundant.
No existing declaration signature or definition changes, and no target meaning changes.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
```

## Users

`tools/downstream.py` with `--allow-missing --uses
AlgebraicGeometry.derivedDirectImageComposition_associativity` reports zero active
consumers because this module is quarantined. Searching both library roots and
quarantine finds the following sole direct consumer. It already publicly imports
SchemeDerivedDirectImage independently, and applies the unchanged theorem directly.
No consumer adaptation is necessary or delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | unclaimed | Quarantined; its own public import already supplies this interface. The associativity application retains exactly its old type. |

## Status

landed 20261020T145508-L-2402291 2026-10-20 (merge of deliver/F6/Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity)
