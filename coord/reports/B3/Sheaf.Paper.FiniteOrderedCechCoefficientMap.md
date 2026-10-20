## What changed

Restored `lean/Sheaf/Paper/FiniteOrderedCechCoefficientMap.lean` from its
`coord/rework.tsv` quarantine archive. Repaired the proof of
`AlgebraicGeometry.orderedCechCoefficientMap_zero`: restriction naturality is
proved locally on sections using naturality of the underlying presheaf map,
then transported through extension by zero using
`HomologicalComplex.extendMap_f`. This replaces the reference to an upstream
private theorem. The coefficient map, every signature, and the public import
are identical to the archived module. No source-library file is changed.

The complete module compiled cleanly through `lcompile.py` in 8.0 seconds.
The diff against the quarantine archive changes only the repaired theorem's
proof. All lines satisfy the 100-character limit.

## Proved and sorry left

This is a zero-hole compile repair, not a hole closure. The archive has zero
`sorry`s, and the delivery has zero. Holes closed: none. Holes added: none.
Split off: none.

The repaired theorem is `AlgebraicGeometry.orderedCechCoefficientMap_zero`
(node `lem-weil-pbc-ordered-cech-coefficient-map`). The existing complete
proofs of `coefficient_comm`, `orderedCechCoefficientMap_naturality`, and
`orderedCechCoefficientMap_single_isIso` are preserved.

## No longer needed

None. The existing public import of
`WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex` is required by
the statements and construction. The node's dependencies and its three-step
proof remain accurate. No module or node is withdrawn. In particular the
quarantined consumers still require this coefficient map.

## Where the brief, the DAG or earlier work was wrong

The item was already sorry-free, but the upstream synchronization made
`alternatingCechZero_naturality` private. Its use in the archived proof was
therefore invalid; this is the exact rework diagnostic, not evidence that
the coefficient-map construction should be removed. The proof now establishes
the needed identity without relying on that private name. No definition or
statement repair, consumer adaptation, new node, or change record is needed.

Searches: LeanFinder returned generic augmentation/naturality results;
Loogle found `HomologicalComplex.extendMap_f`; the Mathlib grep confirmed
that lemma and its standard uses. Reading the source module located the
private naturality proof and its elementary presheaf calculation. The DAG
and the proper-base-change unit route are preserved. The restriction argument
uses neither a cover hypothesis nor a nonempty index set, and therefore also
applies to the empty family. The source's ordered complex and global-sections
augmentation were checked in `literature/stacks-project/cohomology.tex`,
labels `definition-ordered-cech-complex` and
`equation-global-sections-to-alternating-cech`.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
