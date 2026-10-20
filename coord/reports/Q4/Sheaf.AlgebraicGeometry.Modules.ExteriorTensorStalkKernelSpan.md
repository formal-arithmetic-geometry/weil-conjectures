## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan (retirement
row 533) in favor of its existing proved WeilConjectures twin. Migrated its DAG
attachment to the upstream theorem, preserving the node and its dependencies.

The sole direct consumer, Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned,
now imports the upstream twin. Added proved private exteriorSheaf_comparison and
exteriorTensor_comparison helpers, conjugated the quotient map, applied the
upstream stalk theorem, and transported the resulting local relation span back.
The consumer's public theorem signature and public imports are verbatim unchanged.
Its private relationSpan_map uses the upstream wedge_map API. Its node describes
the comparison and transport.

The consumer compiled cleanly; #print axioms reports exactly propext,
Classical.choice and Quot.sound. The unchanged immediate downstream consumer
ExteriorTensorKernelRelations compiled against the sandbox overlay. The source
was read at the Riemann–Roch proof of (*), determinant lift-independence paragraph;
the unit record has no realized step replaced by this adaptation.

Change record: coord/changes/Q4-retire-exterior-tensor-stalk-kernel-span.md.

## Proved and sorry left

This is a zero-hole retirement. The item originally contained 0 sorries; none
are closed and none are added or split off. No sorries remain in the delivered
consumer. Its theorem AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span
is proved from the upstream AlgebraicGeometry.Scheme.Modules.exteriorTensor_stalk_kernel_le_relationSpan
with explicit transport of the different exterior-sheaf constructions.
The two new private comparison theorems are completely proved.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan.
The consumer's proof import of that module is replaced by
WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan.
Its duplicate exteriorTensorRelationSpan and exteriorTensorRelationStalkSpan
constructions are replaced by the upstream constructions after comparison.
No DAG node or mathematical dependency is pruned: the stalk-kernel node is still
used through its migrated upstream attachment; the unit route is preserved.
The retired copy's separate private retainedExteriorSheaf_stalk_comparison is
unnecessary: the consumer compares sheaves before invoking the upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes, but the current queue
marks this module as a retirement and its current source has zero holes. The
upstream API difference is substantive: its two relation-span definitions use
exteriorPower, so replacing the import alone does not typecheck. The explicit
comparison above handles that difference without changing the public consumer
statement or any upstream signature, definition or import.

Searches run with msearch.py: LeanFinder for the stalk exterior-quotient kernel
returned exteriorPower.presentation infrastructure; Loogle Submodule.map_span
returned the standard span transport lemma; grep for the kernel theorem returned
zero hits in that service. Direct source search found the exact proved upstream
twin and exactly one direct consumer. No new mathematical statement or node was
needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
