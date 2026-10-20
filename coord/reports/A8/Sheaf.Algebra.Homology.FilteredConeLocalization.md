## What changed

Proved `CategoryTheory.filteredConeLocalization` in
`Sheaf.Algebra.Homology.FilteredConeLocalization`, with its statement unchanged.
The proof uses the existing bounded-below homotopy triangulation, represents the first
arrow of a distinguished triangle by a bounded-below cochain map, and compares its
cone triangle using `isoTriangleOfIso₁₂`. For each grade, the ordinary homotopy
category's acyclic-subcategory cone criterion proves the graded-acyclic equivalence.
Existing filtered localization instances provide the derived triangulation and
exactness; unpacking its essential-image definition gives the final characterization.
Updated the node's proof and dependencies to this route. No definitions or interfaces
changed, and no consumer adaptations are needed.
The module compiled without errors or warnings through `lcompile.py`
(8.0 seconds on the current resumed check).

## Proved and sorry left

Closed 1 hole: `CategoryTheory.filteredConeLocalization`
(node `lem-trf-filtered-cone-localization`). No holes remain in the item; zero holes
were added or split off. This is a proof from existing declarations, including the
still-unproved structural lemmas in `FiniteFilteredLocalization`, as intended by stage 3.

## No longer needed

Removed all eight original proof-only imports:

- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`
- `Mathlib.CategoryTheory.Triangulated.Subcategory`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.CategoryTheory.Localization.Triangulated`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`
- `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`

The necessary Mathlib declarations are already visible through the sole retained
public import `Sheaf.Algebra.Homology.FiniteFilteredLocalization`.
The standalone quasi-isomorphism/cone lemma
`lem-pur-quasi-iso-cone-acyclic` and its source module
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic` are unnecessary:
the homotopy-category acyclic-subcategory criterion applies directly to every
image distinguished triangle. The saturated-system definition
`def-pur-saturated-triangulated-localization` and its module
`WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem` are unnecessary:
the existing localization instances already provide the compatibility hypotheses.
Removed `def-sp-filtration`, `def-sp-filtered-complex-subquotients`,
`def-weil-abstract-derived-category`, and `def-weil-triangulated-category` from the
node's proof dependencies; these remain statement dependencies where already present.
Their definitions and modules still enter through the existing statement interface;
this proof requires no separate construction or theorem from them.
No unit realization is bypassed: the item's unit has no realized statement or steps.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original seven-step plan repeats
bounded-below and localization infrastructure that Mathlib and the existing
`FiniteFilteredLocalization` declarations already supply. The updated route reuses
those declarations rather than reconstructing their structures.
The theorem keeps both filtration-bound cases and its original bound hypothesis;
the infrastructure actually works without using that hypothesis. Zero objects,
identity maps, the zero full subcategory, a one-step interval, and nonuniform bounds
all fit the same argument.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
