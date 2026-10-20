## What changed

Restore `lean/Sheaf/CategoryTheory/DoubleComplexTruncationDecalage.lean` from the
quarantine path recorded in `coord/rework.tsv`, preserving all declarations and
the full proof of `HomologicalComplex₂.totalTruncLEToDecalage_isIso`.
The archived comparison is not withdrawn or replaced by an empty module.

The published dependency artifact for `Sheaf.CategoryTheory.DoubleComplexTotal`
still imports the retired `Sheaf.CategoryTheory.Filtration`; combining it with
the current decalage tower reproduces the recorded duplicate
`CategoryTheory.DecreasingFiltration.IsExhaustive` error. Its current repository
source already publicly imports
`WeilConjectures.CategoryTheory.CanonicalFiltration`. Include that source
byte-for-byte in the compilation packet so the restored comparison is checked
against the corrected dependency rather than the stale compiled artifact.
No existing source-library file, signature, definition or proof is changed.
The restoration record is
`coord/changes/J2-double-complex-truncation-decalage-restoration.md`.

Validation: `lcompile.py --all` compiles DoubleComplexTotal in 2.9 seconds and
the restored comparison in 5.3 seconds, with no errors or warnings. Separate
import probes isolate the collision to the published DoubleComplexTotal
artifact: the current decalage tower, decalage, subquotients and upper-truncation
coordinate modules all import together with CanonicalFiltration successfully.

The proof keeps the finite first-quadrant diagonal decomposition, the boundary
projection calculation, the evaluated cycles-kernel lift, and cancellation of
the totalized monomorphism. Negative truncation indices and total degrees
remain included; no hypothesis is added.

Consumer check: the unmodified archived
`Sheaf.CategoryTheory.SmartTruncationDecalageTower` compiles against the restored
comparison and refreshed total-complex dependency in 9.6 seconds, with no errors
or warnings. Its normalization equation and tower naturality use the preserved
comparison API. The active-library downstream query with `--allow-missing`
returns zero because this module and its direct consumer are quarantined; the
quarantine import scan and the DAG parent check retain that consumer explicitly.

## Proved and sorry left

This is restoration of a quarantined import repair, not a new hole closure.
The archived item has 0 holes; the restored item has 0 holes. Closed: none.
Added: none. Split off: none. No declaration in the delivery contains `sorry`.

The following existing proofs are preserved and compile:
`HomologicalComplex₂.total_truncLE_secondFiltration`,
`HomologicalComplex₂.total_truncLE_decalage_factor`,
`HomologicalComplex₂.totalTruncLEToDecalage_arrow`,
`HomologicalComplex₂.totalTruncLEToDecalage_naturality`,
`HomologicalComplex₂.totalTruncLEToDecalage_mono`, and
`HomologicalComplex₂.totalTruncLEToDecalage_isIso`
(node `lem-sp-double-complex-truncation-decalage`).
The canonical factor remains the unique map characterized by its inclusion
equation; its data is not chosen from an undetermined existence assertion.

## No longer needed

None. Both declared dependencies, `def-sp-double-complex-total` and
`def-sp-filtered-complex-decalage-tower`, are still used. No imports, nodes,
modules, parent dependencies or unit steps are pruned. The DAG attachment
remains unchanged, including the archived parent users.

## Where the brief, the DAG or earlier work was wrong

The assignment is a zero-hole quarantined import repair. The archived module
already contains a complete proof. The rework error persists with the published
DoubleComplexTotal artifact, but disappears when its current repository source
is compiled together with the restored item. Consequently no mathematical
statement or definition repair is necessary. Searches by LeanFinder, Loogle,
and grep found only the generic truncation/totalization APIs; no alternative
complete comparison theorem was substituted.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
