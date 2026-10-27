## What changed

Proof of WeilConjectures.point_derived_tensor_tower_coherence from ordinary scalar
coherence and exact-derived transport. Pairwise coefficient identifications are compared by
their constant equations. Coefficient inclusions compose by uniqueness of their quotient
projections. Normalized ordinary and derived comparisons are transported explicitly, and
uniqueness compares all ten fields of Maps. The exact transport interface
also returns uniqueness from the four representative normalizations across equal
ordinary data; this avoids rebuilding derived coherence during uniqueness. Chain laws are the ordinary laws in each degree.
Flat-term K-flat preservation uses the existing independent-coefficient change-of-rings
result; exact-derived factorization proves counit invertibility.

New general statements separate ordinary tensor/sections coherence with independent
coefficient universes from categorical exact-derived transport. Both general results,
substitution helpers and localization-normalization helpers are proved. The modules
alias uses the definitionally equal completed ring sheaf directly;
scalar functor aliases have explicit category endpoints. Named proposition clauses share
the types of the law records; the generator is semireducible to avoid unnecessary
unfolding. Change record:
coord/changes/point-tensor-tower-sections-reducibility.md.

## Proved and sorry left

Closed the original hole WeilConjectures.point_derived_tensor_tower_coherence:
one of one, with a complete proof. The two new
results CategoryTheory.SectionsScalarOrdinaryTower.coherence and
CategoryTheory.ScalarTower.exact_transport are proved and have compiled successfully.
Their current axiom checks list only propext, Classical.choice and Quot.sound
(compile e0525401201debe121425994, exit 0).
There are zero written sorry occurrences in all three modules; no holes are split off.
No data definition contains sorry. No holes are added. Both unchanged direct consumers,
Sheaf.Paper.CompletedModelSectionsTransport and Sheaf.Paper.PointInverseImageCoefficientTower,
compiled successfully against the final repaired item in compile
92a76f88a5fb8b8a7fcf442c (exit 0); no consumer adaptations were required.
The item axiom scan retains sorryAx through the existing finite-free/descent and
change-of-rings dependencies, as allowed for this stage; neither new general result
introduces a hole.

## No longer needed

Removed proof imports Sheaf.Paper.KFlatRingedToposPullback,
Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients,
Mathlib.CategoryTheory.Sites.Sheafification, and
Mathlib.CategoryTheory.Localization.Predicate. Their required infrastructure remains
available through the public interfaces actually used.

The main proof does not use lem-weil-sections-scalar-cochain-coherence or
lem-weil-sections-scalar-derived-transport as theorem dependencies: their signatures fix
the coefficient and module universes together and the index set to Fin 4. The two new
general results express the ordinary and exact-localization parts at the independent
universes required by the unchanged item. SectionsScalarCochainCoherence remains transitively imported
for its module-category infrastructure; its declaration has not been removed or changed.

The stale tool approvals lem-pc-kflat-resolution and
lem-weil-pbc-ringed-topos-kflat-pullback are removed from the item's node. All-complex
exactness from point descent gives the representative transport directly. The separate
K-flat preservation clause uses lem-pur-kflat-change-of-rings-independent.
No existing module is withdrawn; no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned generic cochain and derived transport statements force their coefficient
rings to occupy the sheaf-section universe. The point module deliberately keeps the
coefficient universe u independent of the site universe t, with module carriers in
max u (t+1). Specializing the planned statements therefore does not directly typecheck.
The refinements retain the same ordinary and localization arguments and expose the
needed independent universes. Exactness already supplied by point descent permits
ordinary exact localization rather than another K-flat resolution construction.

## New nodes

lem-weil-sections-scalar-ordinary-tower records ordinary balanced associators, inverse and
unit formulas, the sections square, both four-stage equations, and uniqueness with
independent coefficient universes, for an arbitrary preorder.

lem-weil-exact-scalar-tower-transport records unique transport of ordinary scalar coherence
through exact derived functors and prescribed scalar identifications. Its normalization
helpers follow by equality substitution and full faithfulness of localization. Counit
substitution is proved before specialization to completed sheaves.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
