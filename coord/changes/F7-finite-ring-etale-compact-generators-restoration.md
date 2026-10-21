# AlgebraicGeometry.Etale.finiteRing_compactGenerators

## Reason

Restore the quarantined item with its existing complete proof after retirement of
the duplicate compact-object and constructibility-comparison modules. The public
statement needs the canonical compactness definition, and the proof needs the
canonical comparison theorem. The old module is absent from lean/ and retained
unchanged under quarantine/. No definition or mathematical statement changes.

## Old

The archive contains:

```lean
public import Sheaf.CategoryTheory.CompactObject
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
```

Its comparison proof line is:

```lean
        exact (Scheme.isConstructibleEtaleModuleSheaf_iff _).2 (hbc.2 q)
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
```

The comparison proof line becomes:

```lean
        exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
          (hbc.2 q)
```

The theorem signature is identical to the archive. All other proof steps are retained.
The public import supplies the same compactness notion in the restored signature.
No target statement or definition changes, so no target-meaning review is reopened.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators
--uses finiteRing_compactGenerators` reports unknown module because the live item is
quarantined. Searches of both lean/ and quarantine/ find no live importer and these
four archived importers. All are preserved and need no forced adaptation: the restored
theorem has exactly the old signature, and source compactness is the shared notion.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | F7 | Restore the module and migrate two imports and one proof reference. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | Unclaimed in current local records | Archived consumer; theorem signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | Unclaimed in current local records | Archived consumer; theorem signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Archived importer; public source compactness restored; no edit. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | Unclaimed in current local records | Archived importer; theorem signature unchanged; no edit. |

No quarantined consumer is deleted or replaced by an empty module. All dependency
edges and parent obligations are retained. Independent review should compare the
restored module against its archive and check the public signature unchanged.

## Status

landed 20261021T143903-L-16708 2026-10-21 (merge of deliver/F7/Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators)
