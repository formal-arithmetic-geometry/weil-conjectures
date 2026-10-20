## What changed

Completed the retirement repair listed in coord/retire-items.tsv, rather than
changing an already complete proof. Withdrew the duplicate module
Sheaf.AlgebraicGeometry.PicardTensorFrameCoordinates through deleted.txt and
reattached lem-sc-picard-tensor-frame-map to the same theorem in
WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates.

The only remaining consumer was the unclaimed module
Sheaf.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized. Replaced its
identical implementation with a public import of its adopted source twin and
reattached lem-sc-picard-tensor-frame-restriction-normalized there. All
WeilConjectures sources are unchanged.

The source unit isomorphism has the name picardTensorFrameUnitIso. Its construction
is definitionally equal to the former picardTensorUnitIsoFrame (checked by rfl).
After replacing that name, the coordinates module agrees with the source twin
apart from the copyright header; the normalized module also differs only in its
copyright header and import root. Thus the formulas and proofs retain their
meaning without an added compatibility definition or a second proof.

Remote compilation checked the former frame-map statement against the source
proof, its m=0 specialization, and the unit equality. The axiom checks for
picardTensorFrameUnitIso, picardTensorFreeIso, picardUnitHomTopEquiv,
picardHomCongr, picardTensorScalarCoordinate, picardTensorVectorCoordinate,
picardTensorFrame_map and picardTensorFrame_restriction_normalized report only
propext, Classical.choice and Quot.sound.

Change record: coord/changes/retire-picard-tensor-frame-coordinates.md.

## Proved and sorry left

The item originally had zero sorries. Holes closed: 0. Holes added: 0.
Split-off statements: 0. No sorry remains in either delivered module.
The existing source proofs of AlgebraicGeometry.Scheme.Modules.picardTensorFrame_map
(node lem-sc-picard-tensor-frame-map) and
AlgebraicGeometry.Scheme.picardTensorFrame_restriction_normalized
(node lem-sc-picard-tensor-frame-restriction-normalized) are preserved and
contain no sorry or nonstandard axiom. This is a duplicate retirement, not a
new proof or a decomposition.

## No longer needed

Sheaf.AlgebraicGeometry.PicardTensorFrameCoordinates is withdrawn and has no
remaining importers. Its public imports of
WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf and
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf are removed from the
withdrawn copy; the adopted source proof still uses these mathematical tools.

The normalized consumer no longer imports the retired coordinates module,
WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles or
WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections directly. It
re-exports WeilConjectures.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized,
which retains the complete existing proof and required imports.

Neither mathematical node is pruned: both are reattached to the adopted source.
No proof dependency, unit step or tool approval is removed, and no source
library declaration is removed. The sole source-only unit name is now used
through the adopted coordinate definitions.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief suggests a hole, but the live queue marks this item
retire, with zero holes. The retire inventory describes several definitions as
changed. A full comparison shows only a rename of the pinned unit isomorphism;
its body is identical, and all dependent bodies become textually identical after
that rename. The claimed private-helper differences do not require any new
public API: the normalized consumer has the same private helpers in its own
adopted twin. It is unclaimed, so its duplicate implementation can be retired
with this item under the unclaimed-module rule.

The inventory's second consumer, Sheaf.AlgebraicGeometry.PicardTensorFrameRestriction,
was retired independently during this session. A fresh import/use search found
only PicardTensorFrameRestrictionNormalized, and found no users of that
normalized theorem outside its own module. The node mathematical statements and
unit route are unchanged. No new nodes or statements are needed.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
