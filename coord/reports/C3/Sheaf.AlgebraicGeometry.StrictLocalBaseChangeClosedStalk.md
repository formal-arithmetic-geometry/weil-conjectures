## What changed

Completed the retirement repair for Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk.
The assigned file is already a withdrawn stub with zero holes, while its DAG attachment
and two DAG parents still require the original small-colimit model. Preserved that exact
statement, with only a smallModel_ name prefix, in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeClosedStalk. The old collision stays
explicitly withdrawn through deleted.txt.

The complete proof composes the affine presentation with Spec of the inverse canonical
small-to-full colimit isomorphism. The existing structural-map equation identifies the
bottom morphisms; equality transport then applies the fully proved adopted closed-stalk
theorem to the same square. The point field, residue map, sheaf, degree and stalk map stay
unchanged. No definition, target statement or adopted source declaration is changed.

Updated the original node's Lean attachment and proof route. Added a source attachment
for the existing full-model closed-stalk theorem. Both imports used only by the proof are
private. The original signature is mechanically checked equal after just the name change.

Change record: coord/changes/C3-retire-small-model-closed-stalk.md.

## Proved and sorry left

The item starts with 0 sorries and ends with 0. Holes closed: none. Holes added: none.
Split-off statements with holes: none. This is a repair, not a net hole reduction.

Fully proved replacement:
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_closedStalk
(node lem-weil-pbc-strict-local-base-change-closed-stalk).
No sorry remains in any delivered Lean file. The new source attachment references an
already proved adopted theorem and adds no Lean declaration.

The replacement compiles without errors or warnings in 7.1 seconds (an independent
initial compile also passed in 7.5 seconds). A temporary consumer with exactly the original
signature, with both the replacement and adopted theorem imported, compiles cleanly in
2.1 seconds. Printed axioms of the replacement, adopted theorem and structural-map
comparison are exactly propext, Classical.choice and Quot.sound. The consumer is excluded
from the delivered Lean tree; its source is retained in scratchpad/ClosedStalkConsumer.lean.txt.

## No longer needed

The old Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk collision stays retired;
its mathematics is preserved in the distinctly named replacement. There is no new net
module pruning, since the old source is already a stub with no Lean importers.

The replacement does not directly import or reconstruct the old model-global-homology,
strictly henselian sections/stalk, or geometric-field-extension argument. Thus its direct
proof dependencies no longer include
lem-weil-pbc-strict-local-base-change-model-global-homology,
lem-weil-pbc-strictly-henselian-sections-stalk, or
lem-weil-pbc-geometric-point-field-extension. The latter two remain needed by the adopted
full-model theorem and are recorded on its source attachment; they are not withdrawn.
The small-model model-global-homology theorem is not needed on this direct route and is
unchanged. No existing imports were removed from adopted files.

The only direct proof dependencies are the existing canonical structural-map comparison
and the adopted full-model closed-stalk theorem. Both original DAG parents still cite the
unchanged original node id, and its mathematical statement remains exactly available.
Unit sk-thm-p1 and all its realized statements and steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief assumes an extant holed item source. The current retirement row
and source instead show a withdrawn stub, zero holes, and an original small-model DAG
attachment. The adopted theorem uses strictLocalization and strictLocalizationToBase,
whereas the node uses strictHenselizationScheme and strictHenselizationStructuralMap.
Using the adopted theorem without transporting these models would not establish the
attached statement. The canonical comparison supplies that transport, avoiding both a
name collision and another reconstruction of the lower proof chain.

Both listed consumers, StrictHenselizationExchangeCubeStalkIsosSource and
StrictHenselizationExchangeCubeTargetStalkIso, are already withdrawn stubs. Their DAG
parents still require the result, so zero Lean importers is not grounds for detaching it.
No quarantined source or rework row exists for this item. No consumer edit is forced.

## New nodes

src-weil-pbc-strict-localization-closed-stalk records the exact existing adopted theorem
AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk, whose hypotheses
use the full strictLocalization model. Its source is the adopted proof and Stacks Tags
03Q9/03QO; the proof combines model-global-homology, strictly henselian closed-point germs
and geometric-field-extension naturality. LeanFinder, Loogle, LeanSearch and Mathlib grep
found no exact Mathlib theorem; source-tree rg found the complete adopted theorem and the
canonical small-to-full structural-map comparison. This node adds no hole or declaration.

Change record: coord/changes/C3-retire-small-model-closed-stalk.md.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
