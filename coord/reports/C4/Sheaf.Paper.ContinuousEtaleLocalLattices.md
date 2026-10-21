## What changed

Restored Sheaf.Paper.ContinuousEtaleLocalLattices from the precise quarantine path
in coord/rework.tsv. The module had been removed after a cluster restore, while its
DAG attachment and the quarantined stratified-lattice consumer still need it.
The archived module compiles cleanly against the current restored dependencies
(3.1 seconds). The restored Lean source is identical to the archive: its theorem,
private helpers, public imports, and proof imports are all preserved.

The proof applies continuousLisse_affine_etale_lattice pointwise, selects a finite
subcover using openness of etale maps and compactness, proves the coproduct cover
etale, surjective and affine, then applies
continuousLattice_finite_coproduct_of_coefficients to assemble the supplied lattices.
This is the existing DAG route, including arbitrary finite index types, zero ranks
and the empty base. No unit route changes.

Updated only proof_origin on lem-weil-pbc-continuous-etale-local-lattice to record
this restoration. Change record:
coord/changes/C4-continuous-etale-local-lattices-restoration.md.

## Proved and sorry left

Zero local holes in the archived source and zero after restoration. Zero holes
closed, zero holes added, zero split off. This is a missing-module repair rather
than a new proof or a decomposition.

Restored the complete proof of
AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_etale_lattice
(lem-weil-pbc-continuous-etale-local-lattice), together with the fully proved private
helpers finite_affine_etale_cover_geometry,
etale_lattice_of_finite_affine_lattices, and
exists_finite_affine_etale_cover_with_property. No sorry remains in this module
and none is added elsewhere. Imported declarations retain their existing proof status.

## No longer needed

None. Every archived import is retained: ContinuousIntegralCoefficients and Etale
supply statement vocabulary; UniversallyOpen supplies openness;
ContinuousAffineEtaleLattice supplies point neighborhoods;
ContinuousLatticeFiniteCoproduct supplies their assembly. All four existing proof
dependencies remain needed. No node or module is withdrawn or pruned.

LeanFinder found affine-cover APIs but no substitute for the etale-neighborhood
lattice theorem. Loogle identified IsCompact.elim_finite_subcover, which the archived
proof already uses. Source searches confirmed the existing openness and finite
coproduct affineness APIs and found no duplicate of the public lattice theorem.

## Where the brief, the DAG or earlier work was wrong

The assignment is a quarantine restoration with an already complete proof,
rather than a fresh sorry. Restoring its missing file is the required repair;
its absence is not evidence of redundancy. No mathematical statement defect or
proof-plan defect was found. The current C4 return file has no return for this item;
the rework row identifies the precise source to restore. The shared claim snapshot
has no lock for this item; this session follows the explicit dispatcher assignment.

The quarantined ContinuousLisseStratifiedLattices consumer retains its exact theorem
interface. Its complete file still has other quarantined dependencies, which this
delivery does not restore or modify.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
