## What changed

Restored `Sheaf.CategoryTheory.BrownTelescopeAssembly` from its current rework archive.
Changed its public compactness import from the withdrawn
`Sheaf.CategoryTheory.CompactObject` to
`WeilConjectures.CategoryTheory.CompactObject`.
All remaining source text, including `CategoryTheory.brownTelescopeAssembly` and its
complete proof, is unchanged. This repairs the import collision recorded in
`coord/rework.tsv` and the subsequent missing-public-declaration error after K9's
retirement. Change record: `coord/changes/Q4-brown-telescope-canonical-compactness.md`.

The restored theorem follows all four existing node steps: compactness under shifts,
the telescope triangle, lifting compatible stage elements by homological exactness,
and compact-Hom factorization. Its node and unit route require no changes.
The existing declared dependencies remain in use. LeanFinder returned unrelated
successor constructions, Loogle did not index the project telescope declaration,
and Mathlib grep returned no replacement. Direct source inspection found the existing
`WeilConjectures.CategoryTheory.CompactHomHocolim` proof already used by the archive.

## Proved and sorry left

This is an assigned zero-hole repair: 0 holes before, 0 after; 0 holes closed and
0 holes added. No split-off statements. `CategoryTheory.brownTelescopeAssembly`
(node `lem-pc-brown-telescope-assembly`) retains its complete proof.
The private `compact_shift` helper is also proved. No remaining `sorry` declarations.

The repaired file compiles cleanly in 1.7 seconds. A separate compile with
`#print axioms CategoryTheory.brownTelescopeAssembly` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed import: `Sheaf.CategoryTheory.CompactObject`, already withdrawn by K9.
Its replacement exports the canonical, identical compactness definition.
No mathematical node, proof dependency, or additional module is pruned.
In particular the existing telescope and BrownStageSequence helper imports stay needed.
The quarantined file and its Lean attachment are restored, not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished theorem, but the current assignment is
the recorded upstream-sync import repair and its archived source has zero holes.
The previous compactness duplicate was retired after quarantine, so simply restoring
the archive leaves `IsCompactObject` available only through a private proof import.
A direct public canonical import fixes that boundary. No mathematical statement,
definition, or DAG correction is needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
