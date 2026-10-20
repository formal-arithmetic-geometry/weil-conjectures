## What changed

Completed the listed retirement of the duplicate
Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology. Withdraw it through deleted.txt
and repoint lem-sc-finite-free-hom-complex-qc-cohomology to the existing adopted source
module WeilConjectures.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology.
Its theorem AlgebraicGeometry.finiteFree_homComplex_qc_cohomology has exactly the same
signature and induction proof. No source-library file or target statement changes.
Change record: coord/changes/retire-finite-free-hom-complex-qc-cohomology-T2.md.

## Proved and sorry left

The assigned Sheaf module has zero local holes before retirement. Holes closed: 0 of 0.
Holes added: 0. Split off: 0. No sorry remains in the item. The retained source theorem
AlgebraicGeometry.finiteFree_homComplex_qc_cohomology is already proved; this delivery
claims retirement progress only, not a new proof. Both original modules compile alone (Sheaf: 18.4 s; source: 18.5 s). A separate source
probe compiled in 20.0 s and printed exactly propext, Classical.choice, and Quot.sound.
The source probe was removed from the packet after verification.

## No longer needed

Retire only Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology and its duplicate
declaration. Its public imports were WeilConjectures.AlgebraicGeometry.DerivedCategory,
WeilConjectures.Algebra.Homology.HomComplex, and Mathlib.Algebra.Category.ModuleCat.Sheaf.Free.
Its private imports were WeilConjectures.AlgebraicGeometry.SingleSupportedFiniteFreeHomQC,
WeilConjectures.AlgebraicGeometry.LocalizedComplexQCHomologyExtension,
WeilConjectures.Algebra.Homology.StupidTailHomShortExact,
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact,
WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension,
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel, and
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel. These modules remain in
the library and are not claimed pruned. Every mathematical node and proof dependency
is retained through the identical source theorem.

There are no current Lean importers of the Sheaf path. The DAG parent
new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology still uses the same node
in step 3 and proof_deps; its source module already imports the source twin.
No quarantined parent imports the Sheaf path. The unit realized lists are empty;
no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief refers to outstanding holes, but coord/queue.tsv and
coord/retire-items.tsv assign a retirement. The theorem was proved in the earlier
T1 delivery and subsequently adopted upstream. The inventory's former dependency
obstacles have already been migrated. The remaining difference between the current
twins is copyright text, a heartbeat setting/comment, and one redundant private
source import; the theorem signature and proof agree. The node's Lean attachment
still named the duplicate and is now corrected without changing the mathematics.

LeanFinder, Loogle, and grep searches were run through msearch.py. They found
quasi-coherence and sheaf-Hom ingredients; the exact existing source theorem is the
shortest route, so no new result or proof dependency is introduced.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
