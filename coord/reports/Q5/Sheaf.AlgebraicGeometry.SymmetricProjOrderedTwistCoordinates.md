## What changed

Repaired the false universal claim in
Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates: an arbitrary line
isomorphism need not preserve coordinates. Its corrected theorem assumes equality
on restrictions above affine base opens and proves global equality by an existing
source-library sheaf separatedness theorem. A proved private helper establishes
the general local-to-global implication for arbitrary module morphisms.

Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistLine now retains those local
normalization equations in its existing existential gluing conclusion, as its
original source proof in words intended. The only caller,
Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistGluing, retains and passes them;
its statement is unchanged. Both adapted modules were unclaimed in the current
server records. The matching three DAG nodes and their correction/citer records
are updated. Change record: coord/changes/Q5-ordered-twist-normalization.md.

Validation: all three files compile without warnings in import order, including
the sole direct consumer of both changed interfaces. No target or definition
changes; the unit route is unchanged.

## Proved and sorry left

The item had one sorry and now has zero. The corrected
AlgebraicGeometry.SymmetricProjTautologicalCharts.ordered_twist_coordinate_compatibility
is proved, including its general private hom_ext_on_affine_base helper. The old
false statement is NOT proved: count this as a statement repair, not one original
mathematical hole proved unchanged. No new holes or split-off statements are added.

The existing sorry in
AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_line
(lem-trf-symmetric-proj-ordered-twist-line) remains, now with the necessary local
normalization retained. This strengthened gluing obligation remains the geometric
work; it has not been solved. The unchanged-signature parent
AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_comparison
continues to have a complete proof from that obligation and coordinate descent.
Across the three delivered modules there is one sorry, versus two originally;
this textual decrease includes a corrected false statement and is not claimed
as a proof of that statement.

## No longer needed

Coordinates no longer publicly imports
Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace. Its corrected descent
statement does not use hRel, hAffine, hθ, or hθAffine. Accordingly its node drops
lem-trf-free-projective-bundle-base-change-space from stmt_deps and removes both
old proof_deps: def-per-projective-bundle-quotient-data and
lem-trf-free-projective-bundle-base-change-space. The first is still a statement
dependency. Both modules remain needed for normalized line existence and by other
consumers; no module is withdrawn or claimed globally pruned. Existing data are
used through ProjectiveBundleQuotientData, the only retained public import.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old coordinate statement): compatibility for every t is false.
For S = Spec Q and r = 0, the coordinate quotient is nonzero. Composing t with
multiplication by -1 changes its right-hand side and leaves every supplied
hypothesis unchanged. At most one of t and -t can satisfy the equality. Normalizing
the scheme comparisons does not normalize a line isomorphism.

The earlier split discarded all normalization by returning True from line
existence, then incorrectly claimed every resulting isomorphism preserved the
coordinates. The repair retains that actual gluing datum and proves only its
local-to-global consequence. This strengthens a still-holed auxiliary statement;
it is recorded explicitly rather than counted as proving the original hole.
The sole DAG citer of each corrected node is
lem-trf-symmetric-proj-ordered-twist-gluing, whose statement is preserved and whose
proof is adapted. No new node, new arbitrary witness, or hollow definition is used.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
