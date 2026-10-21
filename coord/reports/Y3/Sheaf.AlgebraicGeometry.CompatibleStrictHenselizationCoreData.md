## What changed

Retired Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData, the zero-hole
duplicate listed as a retirement in the current queue. Attached
compatible-strict-henselization-core-data to the already proved declaration
AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreData in the
upstream module of the same basename. Updated its proof and proof_deps to the
actual upstream core-existence/core-completion assembly. Change record:
coord/changes/Y3-compatible-strict-henselization-core-data-retirement.md.

The only DAG parent, compatible-strict-henselization-residues-core, already has
an upstream attachment whose proof imports and applies this replacement.
Its old Sheaf consumer is empty. Neither parent nor adopted source is edited.

## Proved and sorry left

Zero holes initially; zero closed; zero added; zero split off; zero left.
The replacement theorem and its parent have complete existing proofs.
Server compilation of a scratch module importing both passed in 6.0 seconds.
#print axioms for each reports exactly propext, Classical.choice and Quot.sound.
This delivery completes a duplicate retirement, not a new hole closure.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData.
Its private localizationComparison and localizationComparison_base and its
small-colimit transport proof have no consumers. All five of its imports leave
the retired module: WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap,
WeilConjectures.Mathlib.RingTheory.Henselian,
WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism,
WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence,
and WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion.
The last four remain needed by the upstream assembly. The node no longer
needs direct proof edges to def-weil-pbc-strict-henselization-limit and
def-weil-pbc-strict-henselization-structural-map: the upstream assembly needs
only the two core statements and associativity, without the small-model bridge.
These definitions remain used below and elsewhere; no mathematical node is deleted.
The unit route and the parent's dependency on the item node are retained.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes holes, but the actual queue assignment is
a zero-hole retirement. The old retirement inventory named one Sheaf consumer;
that consumer is already empty and its DAG attachment is already upstream.
The old and upstream theorem signatures differ in the colimit presentation;
we record the exact upstream signature, rather than claiming definitional equality.
No mathematical error or statement weakening is involved.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
