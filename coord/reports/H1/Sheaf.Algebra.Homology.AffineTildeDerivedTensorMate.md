## What changed

Repair the returned delivery 86dddfcac12 against current sheaf-dag. The mate module
publicly imports the complete adopted WeilConjectures implementation, preserving its
five fully qualified public declarations, original types and concrete constructions.
The legacy affineTildeFunctor abbreviation remains available through the representative
interface. The universal counit normalization and pinned schemeDerivedBaseChangeMap
are preserved.

The representative compatibility interface and homology-coordinate interface have now
landed independently. Their current sources and metadata are preserved. The sandbox's
representative source is byte-identical to the current library and is present only for
compilation; deliver3 omits it from the changed files. Its stale node copy is excluded.
Only the mate node's proof-origin note changes; its statement, Lean attachment, proof
steps, dependencies and unit route remain as on the current base.

Change record: coord/changes/h1-affine-tilde-derived-tensor-mate-restore.md. Its old
version is the current live mate file, and its new version is the delivered interface.
It replaces the earlier packet's obsolete representative repair and consumer inventory.

Validation ran on the project server through lcompile.py with local compilation
disabled. The current representative and homology interfaces, repaired mate, unchanged
identity-factorization consumer, original consumer import-set probe and five original
mate-type probes all compiled without warnings. The original types are written verbatim
in examples, including universes, hypotheses and the affineTildeFunctor spelling.
Scratch probes are not delivered. The actual dependency sources are compiled in the
same set, so this check uses the current representative interface rather than its
older published artifact.

#print axioms for the five mate declarations, source comparison, ordinary exchange and
its termwise chain calculation reports only propext, Classical.choice and Quot.sound.

## Proved and sorry left

This is a returned interface repair with zero original holes. Holes closed: 0; holes
added: 0; holes left: 0; split off: 0. No new proof credit is claimed.

The interface exposes the already proved or concretely constructed declarations:
AlgebraicGeometry.affineExactTildeDerived,
AlgebraicGeometry.affineTildeDerivedTensorSourceIso,
AlgebraicGeometry.affineTildeTensorCoefficientComplexMap,
AlgebraicGeometry.affineTildeDerivedTensorToPushforward and
AlgebraicGeometry.exists_affineTildeDerivedTensorMate.

No sorry remains in this module or those adopted implementations. No statement is
weakened and no data construction is left unproved.

## No longer needed

No mathematical node or module is pruned. No source declaration is removed, no rework
archive is deleted and no module is withdrawn. There is no deleted.txt.

The mate's direct imports of
WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap,
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor,
WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat,
Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison and
Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange are replaced by the adopted
mate's public imports. Its legacy representative import remains. The two duplicate
private helpers affineTildeTensorCoefficientComplexMap_tmul and
affineTildeDerivedTensorToPushforward_factor are supplied by the adopted implementation's
complete proofs.

The current downstream.py scan reports zero Lean importers of the Sheaf mate module.
The DAG attachment and parent dependencies are still retained; this is not a withdrawal.
The unchanged identity-factorization theorem now reaches the same adopted declarations
through the homology-coordinate compatibility interface and passes the consumer check.

## Where the brief, the DAG or earlier work was wrong

The reviewer C-86ddd passed the returned packet's mathematical content. Its landing
failed on a reviewer-fix filename: batch_land.fixes expects the change-record alias
h1-affine-tilde-derived-tensor-mate-restore.change.md, whereas the failed command supplied
h1-affine-tilde-derived-tensor-mate-restore.md. The actual delivery path is
coord/changes/h1-affine-tilde-derived-tensor-mate-restore.md. The refreshed record needs
no such override and is included in this delivery.

The previous packet also predates the independently landed representative and homology
interfaces. This repair drops those obsolete adaptations and updates the change record
to current source. The first consumer check encountered the old representative's
duplicate declaration in the published build; compiling the current dependency sources
and consumers together resolved it without changing their source.

The October 14 route note predates the complete adopted proofs. The source comparison,
ordinary exchange and mate assembly are now fully proved and pass the axiom checks.
Reusing them preserves the mathematical route and the unit's statement and proof steps.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
