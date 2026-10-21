## What changed

Proved `AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_homology` in
`Sheaf.Paper.IntegralStratifiedPerfectClosureHomology`, preserving its exact signature.
Added private proof imports of `IntegralStratifiedPerfectClosureTruncation`,
`PbcUniformCompleteTriangulated`, and the proved source-library
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
The proof isolates degree q by two standard truncations, identifies that shifted-heart
object with its cohomology placed in degree q, and shifts it by q to degree zero.
Updated the existing node's proof, proof dependencies, and proof origin accordingly.
Validation: `lcompile.py --all` compiled the unchanged truncation dependency in
3.4 seconds and the proved item in 5.3 seconds, with no warnings. All three new
proof imports passed the source import-cycle checks.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_homology`
(node `lem-weil-pbc-integral-stratified-perfect-closure-homology`).
Zero holes remain in the item. Added zero holes; split off zero statements.
The proof uses the existing separately stated truncation-closure theorem; it does
not use the parent characterization, which already imports this item.

## No longer needed

None. Both original public imports remain. The recorded uniform-complete
triangulation dependency remains necessary for shifts and isomorphism transport.
The proof also needs the existing truncation-closure dependency. No node or module
is withdrawn, and the unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original single-step node cited only triangulation. A triangulated subcategory
need not be closed under standard truncations or cohomology. The existing sibling
truncation theorem supplies the missing input. Its two applications plus the
standard shifted-heart identification suffice, with no new analytic lemma.
The proof does not assert that finite coefficient reduction commutes with truncation.
The published compile environment initially lacked the compiled file for the existing
truncation module. The categorical proof was checked as a fully proved generic scratch theorem.
The supported sandbox `lcompile.py --all` then compiled a verbatim copy of the
existing truncation module and the item. The unchanged copy is only a compile
dependency; it contributes no source change or added hole to the delivery.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
