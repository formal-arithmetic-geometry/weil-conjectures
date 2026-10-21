## What changed

Retire the listed duplicate Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison
through deleted.txt. Reattach lem-sc-etale-units-two-cocycle-comparison to
AlgebraicGeometry.Scheme.twoCocycleClassesEquivCohomologicalBrauerGroup in the
adopted source library and align its proof fields with that construction.

The former exact theorem compiles from that equivalence by Nonempty.intro,
with only propext, Classical.choice and Quot.sound among its axioms (2.3 s).
The source construction's axioms were checked too, with the same result.
No adopted source file, target signature, definition or unit route is changed.
No consumers need adaptation: the inventory consumer was already retired;
current import, declaration, quarantine and active DAG-parent searches are empty.

Change record: coord/changes/J1-retire-etale-units-two-cocycle-comparison.md.

## Proved and sorry left

The item originally contains zero direct sorries. Zero holes closed and zero
holes added; no split-off statements. The old theorem
AlgebraicGeometry.Scheme.nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup
is verified from the retained source equivalence in scratchpad/OldStatement.lean.
No sorry remains in the delivered item, and no theorem with sorry is introduced.
This is retirement of a redundant proof route, not a newly closed hole.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison.

The withdrawn module's imports are no longer needed there:
WeilConjectures.AlgebraicGeometry.Sites.Gm,
WeilConjectures.FieldTheory.GaloisUnitsTwoCocycles,
Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison,
Mathlib.SetTheory.Cardinal.SchroederBernstein,
Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding, and
Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding.
The first two remain needed for the source statement and arrive through its
existing public imports; no source import is removed.

Removed proof dependencies of this node:
lem-sc-etale-units-h2-forward-embedding,
lem-sc-etale-units-h2-reverse-embedding, and
lem-sc-galois-units-homogeneous-comparison. The direct source equivalences
replace both directional embeddings and the Nonempty cochain wrapper.
The proof now depends on lem-sc-etale-galois-units-comparison and
lem-sc-galois-units-homogeneous-cocycle-descent, matching the source's two imports.
No other module is withdrawn or claimed globally unnecessary in this packet.

## Where the brief, the DAG or earlier work was wrong

This is a retirement item, despite the generic brief discussing open proofs.
The conservative inventory said the twin lacks the old Nonempty theorem name;
the existing equivalence proves that exact proposition without extra hypotheses.
The inventory's sole consumer is already an empty withdrawn module.

The existing node's final statement sentence says the comparison does not use
homogeneous cochains, although its previous Lean proof already invoked the
homogeneous comparison. The actual mathematical proposition is unchanged;
the updated proof fields accurately record the homogeneous change of variables
used by the adopted source construction. No statement or definition is weakened.

Searches actually run: msearch.py leanfinder returned Hilbert 90 and discrete
degree-two cohomology results, without an etale degree-two comparison;
msearch.py loogle Equiv.trans returned equivalence composition; msearch.py grep
for the two comparison names returned no Mathlib hit. Direct source search found
the adopted construction, whose signature and body were read and compiled.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
