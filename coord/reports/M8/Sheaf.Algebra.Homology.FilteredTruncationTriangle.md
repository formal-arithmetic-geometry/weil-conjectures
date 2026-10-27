## What changed

Replaced the proof of `CochainComplex.FiniteFiltered.filteredTruncationTriangle`
with a complete assembly from the normalized truncation construction. The original
theorem signature and every field of `FilteredTruncationData` are unchanged.

The item now proves, as private helpers, the equivalence between its bounded-below
complex presentation and the existing uniform presentation, full faithfulness into
the unbounded localization, compatibility with grading and forgetting, support
orthogonality (also after shift), and the pure-grade equivalence. These proofs use
`UniformFiltered.unbounded_truncation` and
`uniformFiltered_bounded_localization_comparison` as the existing stated results;
neither requires enough injectives. The main proof obtains the two universal Hom
bijections and their naturality by triangle-morphism extension, proves uniqueness
of the supported triangle, and constructs placement from the pure-grade equivalence.

Added `Sheaf.Algebra.Homology.FilteredTruncationConstruction`, containing the
explicit structure `FilteredTruncationCore` and its construction theorem. This
retains only the cone-normalized triangulation, exact functors, representative
normalizations, support vanishing, distinguished triangle, and canonical graded
quotient normalization. The universal Hom properties, uniqueness, and pure-grade
equivalence are proved in the item rather than assumed in this construction.

Updated the original DAG proof to this route and added the construction node.
All data definitions have actual bodies; no data is selected from a holed mere
existence theorem in a public definition. The existential construction is unpacked
only in a proposition proof.

## Proved and sorry left

Closed original hole: `CochainComplex.FiniteFiltered.filteredTruncationTriangle`.
Added one hole: `CochainComplex.FiniteFiltered.filteredTruncationCore`
(node `lem-trf-filtered-truncation-construction`). Its proof is exactly `by sorry`;
the complete construction proof is in its docstring and node.

This is a decomposition: one upper hole is replaced by one strictly narrower
construction hole, so the packet makes no claim of a net hole reduction. The
remaining construction is the source's separate construction of the exact
truncation functors and triangle (original steps 1–3 and the canonical subquotient
part of step 6). The universal properties and pure-grade equivalence are no longer
part of any new hole. No other holes are introduced. The item itself has zero
remaining `sorry` occurrences.

Validation: the two delivered modules compile through `lcompile.py`, with a clean
single-file compile of the assembled item. The private orthogonality and pure-grade
proofs were also compiled during development before being incorporated into it.
Edge cases: the zero object and entirely acyclic filtration have all grades zero;
the pure equivalence reflects this to zero. For support cutoffs outside the finite
filtration interval, the support arguments still use the same quantified grade
conditions. The essential-image proof uses one common cohomological lower bound,
including the case of an acyclic surviving grade.

## No longer needed

Removed direct proof imports from the original item:

- `WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`;
- `Sheaf.Algebra.Homology.FilteredConeLocalization`;
- `WeilConjectures.CategoryTheory.Abelian.Filtration`.

The first and third supply statement-level definitions already available through
the retained public import of `FilteredTruncationData` and its dependencies. The
cone-localization result remains needed by the construction node; it is not
withdrawn or globally pruned.

The item's proof no longer directly uses the original roof representation,
localization-triangle construction, triangulated-subcategory cone-system,
long-exact-homology, or localization-universal-property nodes. These remain in
the construction proof where appropriate, or below the existing unbounded and
bounded-comparison declarations. Thus this packet claims no globally pruned
module. All adopted source-library declarations remain present and unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan's mathematics is retained. Its dependencies do not by themselves
provide a directly applicable Lean construction for the uniformly finite complex
presentation: `filteredConeLocalization` concerns the homotopy localization of
termwise filtered objects, whereas this item's localization is defined directly
on uniformly finite filtered complexes. The construction node records the needed
cylinder and uniform-subcategory comparison, rather than confusing those types.

`filteredDerivedHomCalculus` cannot be used to extract the desired structure for
general A: it assumes enough injectives and fixes a different derived universe.
This packet adds neither assumption to the item.

The unbounded truncation and bounded localization comparison have unit
`sk-i-additivity`, outside the current unit's declared closure. They are used only
as general categorical filtered-localization tools, not to replace any realized
unit step; the current unit has no recorded realized nodes. Independent review
should assess this generic-tool use. No maintainer approval field is changed.
The existing triangle-morphism-extension tool use is retained.

## New nodes

`lem-trf-filtered-truncation-construction` states the normalized exact functor and
cone-triangle construction, before universal properties. Its source is Varshavsky
§§5.1.1–5.1.2 and Stacks Tags 05S1–05S3; its four proof steps spell out the uniform
homotopy localization, exact descent, cone-to-quotient comparison, and canonical
graded quotient. Mathlib was searched through LeanSearch, Loogle, and grep; the
whole blueprint was searched for filtered truncation, finding no equivalent node.
Its Lean attachment names both the explicit structure and the construction theorem.
No definition or existing statement changes. The preflight-required proof-context
change record is `coord/changes/filtered-truncation-proof-context.md`; it records
the added namespace openings and elaboration options and all five downstream
modules. No consumer requires an adaptation.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
