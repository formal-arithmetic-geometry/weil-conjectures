## What changed

Retired Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties in favour of the
already-proved official twin WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties.
The file is listed in deleted.txt; the DAG node
lem-pc-affine-koszul-geometric-properties now attaches to the upstream theorem.
Its statement, proof plan, proof dependencies and parent dependency remain unchanged.
No upstream file changes. No consumer adaptations are needed: the former consumer
is already an upstream module and already imports the twin. Searches of both live
Lean roots and quarantine find zero importers of the withdrawn Sheaf module.

Compared the complete theorem signatures byte for byte: identical. Compiled an
example with that original signature using the upstream theorem, importing both
SupportedPerfectDetectorAffineConstruction and AffinePerfectKoszulPrincipalUnitPerfect
from WeilConjectures. lcompile.py succeeded in 3.8 seconds; #print axioms reports only
propext, Classical.choice and Quot.sound. The original finite-tuple and universe
parameters, including r = 0 and the zero-ring case, are preserved exactly.

Change record: coord/changes/retire-affine-koszul-geometric-properties-N3.md.

## Proved and sorry left

This is a listed retirement repair with zero initial holes: proved 0 of 0 sorries,
added 0, split off 0, remaining 0. The complete existing proof of
AlgebraicGeometry.affine_koszul_geometric_properties is preserved in the upstream twin
(node lem-pc-affine-koszul-geometric-properties). No declaration is replaced by sorry.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties.
Its duplicate private helpers koszul_term_free, koszul_term_zero,
koszul_strictly_perfect and stalk_subsingleton_of_zero_over are removed with it.
The official module preserves the complete mathematical argument and required helpers.

Removing the duplicate removes its public imports of
WeilConjectures.AlgebraicGeometry.PerfectComplex,
WeilConjectures.AlgebraicGeometry.KoszulComplex,
Mathlib.AlgebraicGeometry.Modules.Tilde and
Mathlib.Algebra.Homology.Embedding.CochainComplex, and its proof imports of
Mathlib.LinearAlgebra.ExteriorPower.Basis and
WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero.
These remain required by the official proof; none of their nodes or modules is claimed
as mathematically unnecessary. No DAG node is deleted or detached.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief describes a holed module, but the current item is a
human-approved retirement repair in coord/retire-items.tsv with zero holes.
The inventory's former consumer Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction
is already absent; its upstream replacement already imports the official twin.
The inventory's missing helper names refer to private helpers and pose no public
compatibility issue. Their upstream replacements are
exists_tilde_exteriorPower_iso_free and isZero_exteriorPower_finsupp_of_lt.
The stale DAG attachment was the remaining live reference to the duplicate.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
