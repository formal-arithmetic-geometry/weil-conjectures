# Compact support direct-image evaluation decomposition

## Reason

The parent theorem is assembled from two independent component statements. The ordinary
component gives the sectionwise comparison and its elementwise identity; the derived
component takes that comparison as input and supplies the derived square normalization,
unit, and counit equations. The parent statement and all existing declarations retain
their signatures. The two new public component declarations are intentionally the only
new interfaces needed by the parent proof.

## Old

The item had one theorem hole whose proof plan combined the ordinary comparison, the
finite-prefix extension, arbitrary-resolution normalization, and the two mate equations.
No component modules existed.

## New

`Sheaf.TraceFormula.CompactSupportDirectImageOrdinaryEvaluation` introduces the ordinary
sectionwise comparison as a standalone theorem.
`Sheaf.TraceFormula.CompactSupportDirectImageDerivedEvaluation` introduces the strictly
smaller derived and mate-equation theorem, with the ordinary comparison as an explicit
input. `Sheaf.TraceFormula.CompactSupportDirectImageEvaluation` imports both and assembles
their conclusions by tuple introduction. The existing target statement is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.CompactSupportDirectImageEvaluation | F9 | Parent proof imports the two new component modules. |
| Sheaf.TraceFormula.CompactSupportDirectImageOrdinaryEvaluation | F9 | New component module; no existing importer. |
| Sheaf.TraceFormula.CompactSupportDirectImageDerivedEvaluation | F9 | New component module; no existing importer. |

## Status

Prepared for delivery by F9 on 2026-10-27. The component declarations each retain a
single named `sorry` for the next workers; the parent hole is closed by a complete
assembly proof.
