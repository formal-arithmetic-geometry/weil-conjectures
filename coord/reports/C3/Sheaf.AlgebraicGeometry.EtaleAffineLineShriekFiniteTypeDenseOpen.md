## What changed

Restored Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen from the
quarantine path recorded in coord/rework.tsv. Migrated its private constructibility
comparison import to WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
and replaced nine uses of Scheme.isConstructibleEtaleModuleSheaf_iff with the current
Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf.

The archived signature, public imports, docstrings, private finite-complement proof,
and dense-open localization argument are preserved. The existing DAG proof, attachment,
and dependencies already describe the restored proof and require no edit. The quarantined
parent calls the identical signature and requires no adaptation. The live downstream scan
finds no users. Change record: coord/changes/C3-restore-affine-line-shriek-dense-open.md.

Validation: the archived version failed with unknown comparison-theorem identifiers;
the repaired module compiled through lcompile.py in 9.1 seconds without warnings.
LeanFinder, Loogle, remote grep, and local source searches found no shorter replacement
for this dense-open compact-support argument. The existing lisse, quasi-finite, triangle,
constructible-homology, and compact-support exchange APIs implement the node's plan.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 original sorries, 0 closed, 0 added, 0 split off,
and 0 remaining in the delivery. Both
AlgebraicGeometry.affineLine_shriek_constructible_of_finite_complement (private) and
AlgebraicGeometry.exists_dense_open_affineLine_shriek_constructible retain complete proofs
from the stated dependencies. The public theorem realizes
lem-weil-pbc-affine-line-shriek-finite-type-dense-open. This repair does not claim that
all imported dependencies are themselves sorry-free.

## No longer needed

Replaced the retired private import
Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison with the adopted source
module WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison.
No mathematical dependency node is pruned; no other module is withdrawn or pruned.
The quarantined parent and its unfinished proof still need this item's declaration.

## Where the brief, the DAG or earlier work was wrong

The item's absence from lean/ was quarantine, not withdrawal. Its archived proof already
had zero holes, but used the pre-sync comparison name. The repaired module restores the
same mathematics against the adopted upstream API. No change to the node statement or
proof route was necessary. The quarantine archive is preserved untouched.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
