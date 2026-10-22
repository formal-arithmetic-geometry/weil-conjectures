# AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange

## Reason

Assigned quarantined rework repair (coord/rework.tsv, row for
Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange).
The archived theorem has zero holes. Compiling its unchanged source fails on
unknown identifiers strictHenselizationScheme and strictHenselizationStructuralMap:
the public Sheaf structural-map module has been withdrawn and is empty.
Status: repaired and single-file compiled; pending independent review and global build.

## Old

Old public import:
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`.
## New

New public import:
`WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`.
The latter publicly imports the adopted strict-henselization construction and
exports the structural morphism required by the original statement. This is an
import repair, not a mathematical definition or statement change. The theorem
signature and proof are byte-identical to the quarantine archive. In particular,
the original small-colimit-model hypotheses remain; they are not replaced with
the adopted source theorem's canonical strictLocalization hypotheses.

The node retains its Lean attachment, proof, proof dependencies and proof origin.
Its verbatim Lean statement is refreshed to the archive's existing
IsTorsionModuleSheaf spelling (the old record still said IsTorsionSheaf).
No source-library file, definition, target, quarantine archive or dependency
module is edited.

## Users

Searches of lean/Sheaf and quarantine/Sheaf for both the import and theorem name
find one direct consumer:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | quarantined rework | Its existing application takes the exact restored signature; no adaptation is required by this repair. Its own obsolete public structural-map import remains that item's rework. |

There are no live Lean importers of this Sheaf module. The quarantined parent and
its DAG proof still require it; the module is restored, not withdrawn. The adopted
WeilConjectures theorem with the same declaration name uses strictLocalization,
not the small-colimit-model presentation. It is not imported by this packet and
is left unchanged. Existing dependency comparisons provide precisely the original
small-model interface; no declaration is duplicated into a new module.

## Validation

The unchanged archive fails to compile with the missing-identifier diagnostics.
The repaired file compiles through lcompile.py in 21.1 seconds. A textual check
confirms the entire theorem signature and proof are identical to the archive,
zero sorry occurrences, and lines at most 100 characters. Delivery preflight
checks the restored declaration and axioms. No consumer's mathematical statement
changes, and no forced consumer adaptation is included.

## Status

landed 20261022T013404-L-3560907 2026-10-22 (merge of deliver/D2/Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange)
