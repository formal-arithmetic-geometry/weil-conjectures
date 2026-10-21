## What changed

Restored `Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono` from its current
quarantine archive. Replaced its obsolete public import of
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` with
`WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`.
This makes the existing stalk-condition declaration available in the public
theorem signature. Every other line is unchanged.

This repairs the return at `e482bfdb8c3`: the current `sheaf-dag` has no live item
file, and `coord/rework.tsv` still names its preserved quarantine archive.
The A2 claim is present. This packet restores the full archived declaration and
proof at its original Lean path, with the import correction; it neither withdraws
the item nor changes its existing Lean attachment or dependencies. The delivery
tool builds the restoration on the freshly fetched `sheaf-dag`.

The repaired file compiles cleanly in 3.0 seconds against the current published
build (4.0 seconds in the separate consumer-validation set). The new import passes
the import-direction check.
The current node's signature matches the restored theorem verbatim; all its
proof dependencies remain used. The proof follows Stacks `perfect.tex`,
`lemma-single-complex-base-change` (Tag 0DJ9): target locality, the affine case,
source-open induction, gluing and top-open normalization, followed by homology.
The unit record `sk-thm-picard-coherence` is unchanged.

The retained LeanFinder, Loogle and grep searches found no replacement for this argument.
The only direct consumer is the quarantined
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono`; its unchanged source
compiles against the repair in 21.0 seconds. Its validation copy is excluded from
the delivery. A separate import and `#print axioms` probe compiles and reports
only `propext`, `Classical.choice` and `Quot.sound` for the repaired theorem.

Change record: `coord/changes/A2-single-complex-qcqs-stalk-condition-import.md`.

## Proved and sorry left

This is an assigned import repair with zero original holes.
`AlgebraicGeometry.singleComplexBaseChange_homology_mono` keeps its complete proof.
Holes closed: 0 of 0. Holes added: 0. Holes remaining in the delivery: 0.
No theorem is split off.

## No longer needed

Removed the import of the withdrawn, empty
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` module and used its
adopted provider. No mathematical node or proof dependency is pruned. The item's
Lean attachment and all existing DAG dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The quarantine row correctly reports the unknown identifier. The archived source
still imported the retired provider; the current definition node already points
to the adopted provider. The proof and statement require no repair beyond that
import. The public theorem signature is unchanged and no target meaning changes.
The returned delivery was based before the batch rollback. Restoring the current
quarantine archive on the current delivery base preserves the mathematics that
the rollback removed from `lean/`; the archive itself remains untouched.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
