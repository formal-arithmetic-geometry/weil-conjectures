## What changed

Reconstructed the item from the current source named by `coord/rework.tsv`,
`quarantine/Sheaf/AlgebraicGeometry/PicardExternalCoefficientsAffineCechComparison.lean`,
and reapplied the repair after the return of delivery `68760ef877` (base `e0d550965`).
There is currently no live copy under `lean/`; the quarantine archive and its DAG
attachment are preserved. This packet restores the complete module with two edits:

- Replace the public import of
  `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` with
  `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
  The proof dependencies already use this adopted interface; mixing it with the old
  Sheaf interface caused the duplicate `externalCupCoefficients` declaration.
- Apply `HomologicalComplex.homologyMapIso c q` in the final isomorphism composite.
  This dedicated API avoids the expensive elaboration of the generic homology functor.

All declaration signatures, definition bodies, attributes and docstrings are preserved.
The proof still follows the existing node: native affine Cech comparison, the affine
product cover, quasi-coherence, open restriction, and exact scalar forgetting.
No proof-route, node, or consumer changes are required.

The reconstructed module compiled against the current published build in 12.2 seconds
with no errors or warnings. It contains zero `sorry` tokens. The delivery tool runs
its axiom probe and preflight on this same packet.

Change record: `coord/changes/picard-affine-cech-canonical-field-linear-import-A7.md`.

## Proved and sorry left

Assigned repair of an already proved module: 0 of 0 holes closed, 0 holes added,
0 split off, and 0 holes left.
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_affine_cech_comparison`
retains its complete proof for node
`lem-sc-picard-external-coefficients-affine-cech-comparison`.
The private helpers `nativeCechIso` and `tensorPullback_qcoh` remain complete.
There are no declarations containing `sorry` in the delivered module.

## No longer needed

Removed the import of `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`
and replaced it with the adopted upstream interface. The old module is unnecessary
for this item; it is not withdrawn and may still be needed by other consumers.
All eight declared proof dependencies remain needed. No nodes or modules are pruned,
and no new nodes or modules are added.

## Where the brief, the DAG or earlier work was wrong

The return of `68760ef877` reports a file changed after base `e0d550965`, rather than a
mathematical defect. The retained report referred to the earlier return of
`f9fb03e951`; this report and change record now describe the current return and source.
The rework queue records the post-sync duplicate-import error in the quarantined source.
Restoring that source with its canonical import is the substantive repair; no empty
module, withdrawal, or quarantine deletion is proposed. The existing DAG and unit route
already agree with the complete proof.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
