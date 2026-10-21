## What changed

Completed the zero-hole retirement item in coord/retire-items.tsv row 1345.
Withdraw Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue using
deleted.txt and replace its sole consumer's private import by the official
WeilConjectures twin. In determinant_wedgeMorphism_of_local_data, transport the
chosen family through exteriorSheafPowerIso, apply the official family gluing
theorem, and transport the global morphism back. Tensor-section naturality and
the forward/inverse wedge equations prove both formula conversions in Lean.

The consumer's two public signatures, visibility and public imports are unchanged;
its local-data proof and existing private helper are unchanged. No upstream file,
target, or definition is edited. Update new-wedge-glue-family to the official
attachment and proof, and lem-sc-determinant-wedge-morphism-glue to the actual
transport argument. The determinant construction and unit route are preserved.
Change record: coord/changes/J4-retire-determinant-wedge-morphism-glue.md.

Repair of return C-68115 (returned head 681151c2c): compared the retained
packet with the current shared source and retirement records. The consumer
still imports the duplicate on the current base, and the explicit transport
remains the required migration. Recompiled the retained adapted consumer on
the server on 2026-10-21: exit 0, no warnings, 4.8 seconds. The delivery tool
recreates the packet on the freshly fetched sheaf-dag base. The unrelated
QcoherentTensorPullbackSheafMap path from the failed landing is absent from
this packet and is not restored, deleted or otherwise changed here.

## Proved and sorry left

Actual starting item hole count: 0. Holes closed: 0. Holes added: 0.
Split off: 0. Sorries left in delivered Lean files: none.

The retired determinant_wedgeMorphism_glue_family already had a complete proof;
its existing official replacement has a complete proof too. The adapted
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_of_local_data is
proved with the unchanged statement and no sorry. The consumer's
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data and its
private exteriorSheafPowerIso_hom_wedge remain proved unchanged.

Validation: the adapted consumer compiles individually on the server. All six
modules in the downstream scan compiled cleanly against the adapted consumer
(each file within 60 seconds); the
unchanged verification copies are removed from the delivery. The delivery tool
also compiles the delivered module with its axiom and direct-hole probe.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue.
Its sole consumer drops that private import in favour of the official twin.
Its private determinant_liftWedge_kernel_exists_compat and local copy of
exteriorSheafPowerIso_hom_wedge disappear with it; the consumer already has its
own proved forward-wedge helper.

The retired implementation's private import of
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTensorQuotientComparison is no
longer used by this route. Its node lem-sc-exterior-sheaf-tensor-quotient-comparison
is removed from the glue node's proof dependencies; that comparison module still
has another consumer, so this delivery does not withdraw it. The official glue
uses new-exterior-tensor-quotient and new-determinant-lift-wedge-kernel. Both remain
needed and attached to their official declarations. The canonical comparison node
lem-sc-exterior-sheaf-power-comparison is used in the adapted consumer rather than
inside the official glue node. No mathematical node is deleted, and no other
module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief suggests this item has an open proof obligation, but
current source and queue identify a zero-hole retirement. The twin uses a
different implementation of exterior sheaves, so replacing the import alone is
insufficient. Explicit transport preserves the consumer statement exactly.
The old consumer node still described generic sheaf gluing rather than its actual
call to the family theorem; it now describes the Lean transport proof.
No false statement or unit-route defect was found. The transport works also for
rank/degree zero, empty opens/schemes and zero rings. No new nodes were introduced.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
