## What changed

The original first-reduction theorem is proved from its four conclusion theorems.
All seven supporting results are proved in this delivery; no unfinished split is added.
Vanishing uses induction on the existing successive coefficient triangles, followed by
the specified Roos derived-limit triangle. Conservativity uses the cone and vanishing
arguments. The scalar-extension/tensor comparison is proved using K-flat models.
The original statement and all existing signatures are unchanged.

The signed shift comparison of the explicit augmented Roos complex is constructed
directly. The strict Roos construction is an additive functor
with a natural augmentation. Its preservation of degreewise split short exact sequences
is proved using explicit splitting operators. The augmentation's endpoint-to-middle
criterion follows from the derived triangles of short exact sequences. Applying it to
the standard split mapping-cone sequence proves the required cone augmentation criterion.
Triangle closure uses a right-fraction representation, a K-flat resolution and the
isomorphism between distinguished triangles with the same first two vertices.

Validation: the retained zero-hole packet previously passed lcompile.py --all.
On resumption, the mandatory dry run reproduced a 60-second timeout in the
scalar-extension comparison. Its proof now constructs the tensor/scalar comparison
abstractly and supplies the category and both coefficient rings explicitly when
specializing it. This prevents elaboration from unfolding the large inverse-image
and monoidal constructions to infer them. The complete revised comparison compiled
in 34.3 seconds, without warnings; the statement and mathematical argument are unchanged.
The abstract helpers are private, proved, and in the same module. No file or proof was
split to meet the compilation limit, and no compilation limit was raised.

The signed Roos product comparison commutes with every projection, the tower
endomorphism and the tensor units. The two-coordinate comparison uses (-1)^r on its
second coordinate; the matrix equation includes explicit transports between equal
degree indices. The augmentation identity follows by its two projections.
The seven new nodes contain the required logged Mathlib searches, including LeanSearch.
The required resumed dry run passed compilation and preflight, but the following
submission reproduced a 60-second timeout in the signed shift comparison and pushed
nothing. Profiling identified repeated inference through the inverse-image monoidal
construction. Local irreducibility attributes in the two strict Roos modules keep
that construction folded during elaboration. Respecting transparency while comparing
types avoids unfolding the same large instance expressions repeatedly; the strict
functor and signed comparison then compiled in 41.2 and 44.9 seconds respectively.
These local settings change no definition,
statement, or proof argument. No timeout was increased and no module was split.
Earlier compile-server failures and failed preflights pushed nothing.
The parent signature matches the current shared source exactly.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction`.

The new conclusion theorems are proved:
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction_vanishing`,
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction_triangles`,
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction_shifts`, and
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction_isIso`.

Also proved:
`AlgebraicGeometry.ProEtale.derived_nakayama_reduction_comparison`,
and the strict Roos functor, natural augmentation, degreewise split exactness,
`AlgebraicGeometry.ProEtale.AdicCompletion.roos_augmentation_middle` and
`AlgebraicGeometry.ProEtale.AdicCompletion.roos_augmentation_cone`.

Also proved:
`AlgebraicGeometry.ProEtale.derived_nakayama_roos_shift_comparison`, node
`det-pe-derived-nakayama-roos-shift-comparison`. The comparison includes the actual
augmentation equation. Its construction works for every integer r: r=0 gives the
identity sign, even r gives +1 on the second coordinate and odd r gives -1.
No boundedness or completeness hypothesis is required for this chain comparison.

Original holes closed: 1. New holes added: 0. There are zero sorries in the eight
modules of this delivery, and no definition contains sorry. Existing imported
statements such as the successive coefficient triangles, completeness representative
independence and the Roos derived-limit theorem remain dependencies; their proofs
are not claimed here.

## No longer needed

Removed the unused draft proof import
`Mathlib.Algebra.Homology.HomologySequenceLemmas` from the strict Roos functor module;
the final proof uses derived short-exact-sequence triangles directly.

Removed direct parent proof imports:
`Sheaf.Paper.DerivedNakayamaResolution`,
`Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`,
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and
`Mathlib.CategoryTheory.Limits.Shapes.Products`.

Removed the retained draft's imports of `Sheaf.Paper.DerivedNakayamaCompletionFunctor`
from the shift and triangle helpers. That draft module and its unlanded draft node are
not delivered. No construction of an exact completion endofunctor, coherent shifted
natural transformation, or localization/descent of the whole Roos functor is needed.
The explicit split sequence suffices for cone closure, and an individual chain shift
comparison suffices for shifts. The discarded draft was absent from the shared library;
no existing module or DAG node was deleted.

The existing coefficient-resolution and derived-limit modules remain needed by vanishing.
No existing library node or module is asserted to be prunable from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The coefficient-resolution theorem uses an integral derived tensor functor, while the
first-reduction statement uses finite-ring extension followed by exact restriction.
The plan omitted their necessary K-flat comparison; that interface lemma is proved.
A general exact completion endofunctor would be stronger than needed. The degreewise
split mapping-cone sequence avoids it and avoids proving that
countable products are exact again for this closure argument. The unit's successive
triangle, vanishing, cone and conservativity route is retained.

## New nodes

`det-pe-derived-nakayama-first-reduction-vanishing`: successive coefficient triangles,
faithful scalar restriction on homology, the zero product and the Roos triangle.

`det-pe-derived-nakayama-first-reduction-triangles`: represent the first arrow by a
K-flat chain map and use the split cone sequence plus the shift result.

`det-pe-derived-nakayama-first-reduction-shifts`: shift a K-flat representative and
cancel the normalized chain shift comparison of its augmentation.

`det-pe-derived-nakayama-first-reduction-isIso`: triangulated reduction, cone closure,
vanishing and the zero-cone criterion.

`det-pe-derived-nakayama-reduction-comparison`: identify restricted derived scalar
extension with integral derived tensor by the pulled-back finite quotient.

`det-pe-derived-nakayama-roos-functor`: real strict functor and augmentation,
preservation of degreewise split exact sequences, and the cone augmentation criterion.

`det-pe-derived-nakayama-roos-shift-comparison`: proved signed chain isomorphism
of strict Roos complexes with its augmentation equation.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
