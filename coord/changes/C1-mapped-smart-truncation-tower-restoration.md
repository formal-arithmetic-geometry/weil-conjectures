# CategoryTheory.CartanEilenbergPresentation.mappedSmartTruncationTowerIso_naturality

## Reason

Restore the complete quarantined module assigned by coord/rework.tsv. Its source
was removed from lean/ after a collision between the Sheaf and adopted-source
DoubleComplexTotal modules. The source migration in the already-landed
S2-retire-double-complex-total change record has repaired the dependency imports.
This delivery restores the missing module; it does not withdraw the obligation,
replace the module by a stub, or change its mathematical definitions.

The archived item reproduces the recorded collision against the published compiled
dependencies. Recompiling the current DoubleComplexTruncationDecalage and
SmartTruncationDecalageTower sources in the sandbox resolves it. Those two sources
are included unchanged for compilation against the current import migration;
they introduce no further source edits.

## Old

The assigned path lean/Sheaf/CategoryTheory/MappedSmartTruncationTower.lean is
absent. Its complete proved source is preserved at
quarantine/Sheaf/CategoryTheory/MappedSmartTruncationTower.lean.
The archived import block, verbatim, is:

```lean
public import Sheaf.CategoryTheory.ExtendedTruncationMapIso
public import Sheaf.CategoryTheory.SmartTruncationDecalageTower
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import Mathlib.Algebra.Homology.HomologicalComplexLimits
```

## New

The complete archived module is restored verbatim at its assigned Lean path,
including the same import block, the finite-limit preservation proof, all three
concrete mapped-tower constructions, and the complete naturality proof.
The import environment now uses the adopted DoubleComplexTotal provider through
current DoubleComplexTruncationDecalage. No declaration signature, data, proof,
attribute, or visibility changes. The existing node and its dependency fields
are preserved verbatim. No source-library file changes.

## Users

Source-only downstream.py with --allow-missing finds no active Lean importers.
A scan of lean/ and quarantine/ finds the following direct importer and the
following further consumer of the restored names. Their existing DAG parents
remain attached; zero active importers does not warrant withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.MappedSmartTruncationTower | C1 | Complete archived source restored. |
| Sheaf.CategoryTheory.DoubleComplexTruncationDecalage | unclaimed | Unchanged current source recompiled for the sandbox overlay. |
| Sheaf.CategoryTheory.SmartTruncationDecalageTower | unclaimed | Unchanged current source recompiled for the sandbox overlay. |
| Sheaf.CategoryTheory.CartanEilenbergSmartTruncationSpectralObject | quarantined | Exact archived direct consumer compiled unchanged against the restoration. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageSpectralObjectIso | quarantined | Further consumer; all referenced mapped-tower declarations retained verbatim. |

Individual server compilation succeeded for DoubleComplexTruncationDecalage
(18.0 s), SmartTruncationDecalageTower (18.4 s), the restored item (9.3 s), and
the unchanged direct consumer (7.6 s). The consumer's temporary source copy was
removed from the packet after checking. There are no forced adaptations.

## Status

landed 20261021T110957-L-3853254 2026-10-21 (merge of deliver/C1/Sheaf.CategoryTheory.MappedSmartTruncationTower)
