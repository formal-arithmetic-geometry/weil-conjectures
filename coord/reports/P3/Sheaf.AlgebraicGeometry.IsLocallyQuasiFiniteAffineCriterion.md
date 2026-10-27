## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_affine_criterion` in
`Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion`, preserving its signature.
Added the private proof import
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`.
The affine equivalence follows the stated DAG argument. The covering equivalence uses
whole-open singleton covers in the forward direction and the existing comparison with
Mathlib plus `IsZariskiLocalAtSource.iff_exists_resLE` in the reverse direction.
Updated the node's proof and proof origin and the theorem's proof documentation accordingly.

Server single-file compilation passed without warnings (5.4 seconds).
The delivery preflight checks the declaration's axioms independently.
The empty-scheme and empty-cover cases require no nonemptiness assumptions: coverage
is used only at a given source point, and singleton covers exist for every scheme.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_affine_criterion`
(node `lem-a1-scheme-lqf-affine-criterion`). Proved 1 of 1 sorries.
No sorries remain in the item; no holes were added or split off.

## No longer needed

No imports, dependency nodes, or modules are removed. Every original proof dependency
is still used: the affine-open basis remains necessary for the reverse affine criterion,
although choosing affine covers is unnecessary for the forward covering implication.
No new modules are needed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The statement and original proof plan are correct. The forward covering implication
can use trivial whole-open coverings, since this clause does not require affine opens.
The library already proves the comparison with Mathlib's quasi-finiteness predicates,
so the reverse covering implication can reuse Mathlib's locality theorem directly.
The finite-type locality application needs a local `RespectsRight` instance, proved
from the existing open-immersion and composition instances.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
