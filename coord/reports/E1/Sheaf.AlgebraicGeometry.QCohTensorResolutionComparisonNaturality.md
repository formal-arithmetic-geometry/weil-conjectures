## What changed

Repaired return e0bf08fe0 using the current restored
`Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality` as the base.
Preserved its canonical upstream public import and definition, and added an explicit
public import of the Sheaf TensorNaturality compatibility path.

A reproduced two-import failure showed that the unclaimed companion
`Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality` still duplicated the upstream
local instances and tensor-naturality lemmas. Replaced those copies by a public re-export of
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality`. This removes the
remaining conflict between the restored item and the companion used by its coherence
consumers. It does not reintroduce the returned packet's duplicate map definition.

Change record: `coord/changes/E1-qcoh-tensor-comparison-naturality-import-repair.md`.
The item and companion compile without warnings (3.2 s and 1.2 s). The combined-import
regression passes (2.7 s), and both unchanged active consumer sources compile against the
repaired overlay (26.8 s and 12.7 s). Those unchanged consumers emit existing style and
unused-simp warnings; they are not included in the delivery. The two re-exported theorem
signatures match the old copies modulo whitespace.

## Proved and sorry left

Assigned zero-hole import repair: both current baseline modules have zero `sorry`s,
and both delivered modules have zero `sorry`s. Holes closed: 0. Holes added: 0.
No statement is split off. The canonical upstream implementations retain
`AlgebraicGeometry.tensorResolutionRestrictionTensorMap`,
`AlgebraicGeometry.tensorResolution_totalTensor_comp`, and
`AlgebraicGeometry.tensorResolution_restrictedTensor_square` with their existing signatures.
No new theorem or definition is introduced.

## No longer needed

Removed the companion's duplicate implementations and its direct public imports of
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor` and
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyZigzag`; these are publicly
provided by its canonical upstream twin. The companion's old local-instance copies and
proofs are unnecessary because the same declarations are re-exported from upstream.

No module is withdrawn or globally pruned. The item's restored canonical import stays.
No DAG node, proof dependency, unit realization, or quarantined parent is removed.
The old packet's proposed removal of the Sheaf Comparison import is superseded by the
current upstream compatibility implementation; that obsolete patch is not reapplied.

## Where the brief, the DAG or earlier work was wrong

The retained packet was based on an absent, quarantined item. The maintainer restored the
path at 29591bb80c9 as an upstream compatibility import after that packet's base.
Its old local definition would duplicate the canonical upstream definition. This repair
starts with the current file and preserves the upstream implementation.

The restored item still conflicted with the separate Sheaf TensorNaturality path:
compiling both original imports failed because the environment already contained
`AlgebraicGeometry.TensorResolutionTensorNaturality_localInst1`. The archived
TotalCoherence parent reaches those two paths together, so normalizing the unclaimed
companion is necessary for the compatibility repair. No claimed module is adapted.
Neither delivered module has a direct DAG Lean attachment. Existing dependent nodes and
quarantined sources remain intact. No false mathematical statement was found.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
