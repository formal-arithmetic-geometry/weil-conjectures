## What changed

Prove `CochainComplex.exists_filteredProjectiveModel` without changing its signature.
The proof chooses finite projective models for the subcomplex and total complex,
strictifies their homotopy-commuting square using `cone(id X) ⊞ Y`, proves the
quotient map is a quasi-isomorphism by the homology sequences, and lifts the
localized endomorphism using the existing filtered projective comparison.
The model and endomorphism helpers are proved in this delivery; no hole is split off.
The existing node `lem-trf-filtered-projective-model` records this route.
All existing public imports and the public theorem signature are unchanged.
The proof adds imports for perfect triangle closure, the ordinary K-projective
chain-map lifting API, short exact triangles, homology-sequence comparison,
and the bounds API for cochain complexes.

## Proved and sorry left

Closed: `CochainComplex.exists_filteredProjectiveModel`
(node `lem-trf-filtered-projective-model`), the item's sole original hole.
Added holes: none. Remaining holes in the delivered module: none.
The proof uses `CochainComplex.filteredProjectiveComparison`, whose existing
unproved comparison theorem is an intended dependency of this stage.

## No longer needed

No node or module dependency from the original proof is pruned: the filtered
comparison is still needed for the endomorphism lift, and the ordinary
K-projective Hom comparison is still needed for the model.
Removed the redundant direct proof imports
`Mathlib.Algebra.Homology.DerivedCategory.KProjective` (provided by the imported
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective`) and
`WeilConjectures.CategoryTheory.Abelian.Filtration` (provided by the still-used
filtered comparison module). Their nodes remain dependencies; no module leaves
the targets' import closure through this import cleanup.
The good-truncation and bounded-above filtered replacement of the old node's
steps 1–2 are unnecessary in this proof. Perfectness of the total complex follows
from the existing proved triangle-closure theorem, and a cone of the identity
rectifies the square directly. The block extension-class transfer from the old
steps 3–4 is replaced by this explicit construction.
Never-delivered draft helper modules `FilteredProjectiveModelCore` and
`FilteredProjectiveEndomorphismLift` are consolidated into private proved helpers
of the item and do not become new library modules or new work items.

## Where the brief, the DAG or earlier work was wrong

The retained draft's core helper had no proof, and its proposed public split had
neither its own node nor a valid new-node record. This delivery completes the
construction instead of moving the hole. The original node's route is true but
longer than necessary: finite-projective models for the subcomplex and total
complex suffice. A homotopy-commuting square must still be rectified to a genuine
filtered quasi-isomorphism; no classification by triangles is assumed.
The unit route is preserved (`sk-p-trace` has no additional realized substeps
constraining this support node). No target, definition, or public signature changes.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
