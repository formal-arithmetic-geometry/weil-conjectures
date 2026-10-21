# AlgebraicGeometry.Etale.finiteTorConstructible_etale_compact

## Reason

Restore the quarantined module listed in coord/rework.tsv. Its archived public import
of Sheaf.CategoryTheory.CompactObject points to a withdrawn, empty module. The same
fully qualified compactness definition now lives in the adopted source library.
The theorem's public statement must import that definition publicly rather than
relying on the private proof import of FiniteRingEtaleCompactGenerators.

## Old

```lean
public import Sheaf.CategoryTheory.CompactObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

The complete archived theorem, including its signature, docstring and proof, is
preserved verbatim. The canonical definition has the same name, universes, arguments
and direct-sum comparison body. No mathematical definition or target statement changes.
The DAG attachment and the existing single proof dependency remain unchanged.
No target-meaning review is reopened.

## Users

The downstream command reports unknown module because the assigned module is absent
from lean/ while quarantined. A scan of lean/ and quarantine/ finds no live Lean
importer and exactly the two archived consumers below. Both call the same theorem
with unchanged arguments; neither requires adaptation. Their archives are preserved.
Current claim files were checked; neither consumer has a claim in the local snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | D8 | Restore archive and replace its stale public compactness import. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | Identical public theorem and canonical compactness notion; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Identical public theorem and canonical compactness notion; no adaptation. |

An independent reader should compare the restored source with its quarantine archive:
the import replacement above is the only difference. There is no definition repair,
forced consumer adaptation, withdrawn declaration, or new proof obligation.

## Status

landed 20261021T165811-L-2248967 2026-10-21 (merge of deliver/D8/Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact)
