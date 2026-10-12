## What changed

Proved `AlgebraicGeometry.Scheme.rational_point_base_change_stalk` without changing its
signature, visibility, or existing docstring. The proof constructs a rational section through
P using the finite residue field and algebraic closure, identifies P' with its scalar extension,
shows P' is closed, constructs both DVR instances, and converts irreducibility into generation
of the maximal ideal.

Added the fully proved module `Sheaf.AlgebraicGeometry.RationalPointBaseChangeMaximalIdeal`
with `AlgebraicGeometry.Scheme.rational_point_base_change_maximalIdeal`. This general lemma
requires only a rational section and an arbitrary extension of fields. Pullback pasting,
closed-immersion stalk kernels, and the existing affine ideal-extension formula prove the
maximal-ideal equality directly. Its private helper `ker_stalkMap_field` is also proved.

Added a proof-only import of this module and removed the two unused proof imports listed below.
Updated the item's DAG proof, proof_deps and proof_origin, and recorded the new proved lemma.
No existing public interface changes and no forced adaptations.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Scheme.rational_point_base_change_stalk`
(node `lem-sc-rational-point-base-change-stalk`).

Also proved `AlgebraicGeometry.Scheme.rational_point_base_change_maximalIdeal`
(node `lem-sc-rational-point-base-change-maximal-ideal`) and its private helper
`AlgebraicGeometry.ker_stalkMap_field`. No sorry remains in either delivered module; no holes
were added or split off. Both modules compile cleanly with lcompile.py. This closes the local
proof, while existing imported dependencies retain their own proof obligations.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder`, corresponding to
`lem-sc-dvr-field-extension-order`. The proof needs neither a tensor-product fraction field,
valuation equality, nor a separately constructed tensor-localization DVR. It obtains both
actual stalk DVRs from smoothness and dimension, and compares their maximal ideals directly.

Removed proof import `Sheaf.RingTheory.FibrePrimesResidueFields`, corresponding to
`lem-weil-pbc-fibre-ring-primes-residue-fields`. The existing rational-point uniqueness lemma
and closed-immersion kernel formulas replace the explicit fibre-prime correspondence.

These are the two original proof dependency nodes removed. All four remaining original nodes
(`lem-sc-base-change-curve`, `lem-sc-smooth-regular`, `lem-sc-regular-connected-integral`,
`lem-sc-regular-dim1-dvr`) remain needed. No assertion is made that the removed modules are
unreachable from other targets: the maintainer determines global pruning.

## Where the brief, the DAG or earlier work was wrong

The original plan describes a valid mathematical route, but its stated
`dvr_field_extension_order` requires additional fraction-field and compatibility data irrelevant
to this conclusion. The source library already proves the affine extension formula
`Scheme.IdealSheafData.ideal_comap_appLE` and the closed-immersion formula
`Scheme.Hom.ker_stalkMap`; combining them is enough. No statement was disputed or weakened.
The original theorem docstring is preserved, and its old tensor-localization route is superseded
by the updated DAG proof and the new lemma's docstring.

The new lemma was checked on identity extensions, X = Spec k (both maximal ideals zero),
nonreduced affine schemes (the closed-section kernel argument still applies), and extensions
with transcendental elements. It uses no finite-type, smoothness, dimension, or algebraic-closure
hypothesis. Every map is the actual canonical stalk map, with germ compatibility proved in Lean.

The unit's boundary-point order comparison remains the route: only its local algebra below the
unit has changed. LeanSearch returned an Internal Server Error; this is recorded as unavailable,
not as an absence result. Loogle, LeanFinder, Mathlib source searches, upstream source searches,
and the blueprint rational-point search were performed. The literature files named by the
inherited source records are not present on this machine; the argument is recorded as
agent-written and uses the available, proved Lean declarations.

## New nodes

`lem-sc-rational-point-base-change-maximal-ideal`, in
`dag/nodes/sec-curve-estimates/lem-sc-rational-point-base-change-maximal-ideal.json`, records the
fully proved theorem of `Sheaf.AlgebraicGeometry.RationalPointBaseChangeMaximalIdeal`.
It expresses the geometric maximal-ideal calculation strictly below uniformizer preservation,
with a complete natural-language proof and the actual search results. No new sorry and no
change record is needed, since no existing interface changes.

## Second reading by Q3

1. **Interfaces — pass.** Compared the complete item against the repository with `diff`.
   The existing theorem signature, visibility and docstring are byte for byte unchanged;
   only its proof and proof-only imports differ. The other module and its public theorem
   are new. There are no definition changes, change records or forced adaptations.
2. **Proof and axioms — pass.** Independently compiled both delivered modules in import
   order with `lcompile.py`, without errors or warnings. Neither module contains `sorry`,
   forbidden declarations, or hollow definitions. Scratch-copy `#print axioms` gives only
   `propext`, `Classical.choice`, `Quot.sound` for the new theorem and private helper. The
   original theorem also has `sorryAx` through existing imported dependencies; this delivery
   closes its own hole without claiming its entire dependency closure is finished. The
   rational point is constructed from the actual residue-field isomorphism, not an arbitrary
   witness from an unproved existence statement.
3. **Intermediate statements — pass.** No statements are split off with `sorry`. The fully
   proved maximal-ideal theorem is strictly intermediate and uses the actual stalk map. Its
   identity-extension and Spec-field cases give the expected equalities; the closed-section
   ideal calculation also applies to nonreduced schemes and transcendental field extensions.
   Independent searches used the phrases "maximal ideal of a rational section remains its
   defining ideal under extension of the ground field" (LeanFinder),
   `RingHom.ker, IsLocalRing.maximalIdeal` (Loogle), and
   `ker_stalkMap|germ_stalkMap|map_eq_maximalIdeal` (Mathlib grep), plus searches of both
   library roots. These found constituent local-ring, localization and germ results, not a
   duplicate scalar-extension theorem. The upstream DVR irreducibility lemma expresses the
   same final three-line argument via an extra algebra instance, so no replacement is needed.
4. **Route and pruning — pass after import repair.** The rational-section ideal calculation
   is a shorter route below the unit level. Read `dag/units/sk-prop-ext-invariance.json`:
   its affine boundary-divisor comparison is retained; the unit's `realized` fields are empty
   in the repository and this item is not its key node, so this delivery does not alter them.
   Both removed original proof dependencies are listed under `No longer needed`; all four
   retained original dependencies are used. No claim of global unreachability is made.
5. **Nodes — pass after record repair.** Checked both node statements against the Lean and
   checked each step and its dependency union. The new node has source, proof, origin,
   searches, creation, blueprint, chapter, unit and Lean records. Removed the indirect
   localization-quotient dependency: the proof instead applies the already proved upstream
   `ker_stalkMap` directly. Stored the new Lean signature verbatim, including line breaks.

Changes made by this reader: narrowed the new module's public import from `DensePoints` to
`WeilConjectures.ZetaSeries`, which exports the `fieldPoints` definition used in its signature;
made `DensePoints` and `LocalRing.RingHom.Basic` proof-only imports; added the explicit
proof-only `DensePoints` import to the original module; corrected the new node's proof
record and signature formatting. No proof body or mathematical statement needed repair.
