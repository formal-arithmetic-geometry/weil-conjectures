## What changed

Proved `CategoryTheory.exists_derivedLimit_morphism` in
`Sheaf.CategoryTheory.Triangulated.DerivedLimitMorphism`, preserving its signature.
Naturality on each successor arrow gives compatibility of the tower components.
The proved `towerTransitionEndomorphism_natural_backward` gives the product square;
Mathlib's `Pretriangulated.complete_distinguished_triangle_morphism₁` then supplies
both required equations for the specified Roos triangles. This is the original
TR2/TR3 argument, using its existing implementation rather than repeating the
rotation and full-faithful shift calculation. The unit route is unchanged.
Updated the node's proof and proof origin to describe these applications.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.exists_derivedLimit_morphism`
(node `lem-weil-derived-limit-morphism`). No holes added or split off; none remain
in the delivered module. The single-file server compile passed without warnings.

## No longer needed

Removed the redundant proof import
`WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`: its declarations
are already publicly available through the existing
`Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism` import.
No dependency nodes or modules are pruned: all four declared proof dependencies
are used, either directly or by the existing product-naturality and triangle
completion lemmas. No additional intermediate statement is needed.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error found. The DAG's argument is valid; its rotation,
sign cancellation and full-faithful shift steps already have a Mathlib lemma.
Read the source remark in `literature/stacks-project/derived.tex` and the signatures
and implementations of the transition and triangle-completion lemmas. Loogle,
LeanFinder and grep searches through msearch found the generic completion lemma;
local source searches found the proved product-naturality lemma and no duplicate
of this full tower statement. All products and the given connecting maps remain
exactly those of the original statement; no uniqueness is asserted.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
