# AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison

## Reason

Restore the quarantined rework item listed in coord/rework.tsv. The archive contains a
complete proof and zero sorry holes, but its public structural-map import is now an empty,
withdrawn module. Compiling the original archive on the project server reports unknown
identifiers strictHenselizationScheme and strictHenselizationStructuralMap in the public
signature, with the corresponding WeilConjectures owners suggested by the compiler.

## Old

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
```

The adopted structural-map module publicly imports the strict-henselization construction.
It supplies exactly the small-colimit model and structural map used by the archive.
The restored theorem signature, docstring and complete proof are byte-identical to the
archive. Its two proof imports and both DAG proof dependencies stay in place. The existing
node's Lean statement is refreshed from the archive; its stale IsTorsionSheaf spelling is
replaced by the archive's existing IsTorsionModuleSheaf spelling. No mathematical statement,
definition, target or unit route changes.

The similarly named adopted source comparison has canonical strictLocalization hypotheses;
it is not a replacement for this small-colimit-model theorem. Its declarations and imports
are untouched. The quarantine archive remains untouched.

## Users

The source-only downstream census with --allow-missing lists zero live importers of this
quarantined Sheaf module. A search of lean and quarantine finds no importing parent to
adapt. The parent DAG obligation still cites this node and is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | C3 | Restore the archived theorem; repair only its public structural-map import. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unmodified source | Imports the canonical source comparison; no adaptation. Its associated DAG node still cites this comparison node. |

## Status

landed 20261022T022023-L-429168 2026-10-22 (merge of deliver/C3/Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison)
