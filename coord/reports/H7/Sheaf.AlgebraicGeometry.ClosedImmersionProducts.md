## What changed

Proved `AlgebraicGeometry.closedImmersion_comp_products_and_finiteType_openImmersion`
in `Sheaf.AlgebraicGeometry.ClosedImmersionProducts` without changing its statement,
definitions, imports, visibility, or docstring. Composition uses Mathlib's
`IsClosedImmersion.comp`. The product clause uses `MorphismProperty.pullbackMap`,
which factors the induced map into base changes and composes them, using the
closed-immersion base-change and composition instances already specified by the DAG.
The equations with a trailing identity are converted using `Category.comp_id`.
The last clause uses the open-immersion locally-of-finite-type instance and retains
the supplied quasi-compactness proof.

The server single-file compile succeeded in 2.4 seconds without warnings.
Lean Finder found the closed-immersion pullback instances; Loogle did not resolve
the unqualified `MorphismProperty.pullbackMap` query; grep and direct source reading
located its exact signature and its already proved use in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`. No source-library
import is necessary because the existing Mathlib imports supply the whole proof.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.closedImmersion_comp_products_and_finiteType_openImmersion`
(node `lem-weil-pbc-closed-immersion-products`).

No sorry remains in the item. No holes were added and no statements were split off.

## No longer needed

None. Both existing public Mathlib imports remain necessary for the unchanged
statement and proof. All three declared proof dependencies are used through their
Mathlib declarations: `lem-weil-pbc-closed-immersion-comp`,
`lem-weil-pbc-closed-immersion-base-change`, and
`lem-weil-pbc-qc-open-immersion-finite-type`. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The proof follows the existing DAG plan;
Mathlib already packages its two base changes and composition in `pullbackMap`.
The original quasi-compactness hypothesis in the finite-type clause is preserved.
The unit record has no realized statement or steps attached to this node, and no
unit route is bypassed. The current blueprint places this lemma under
`sec-nagata-compactification/sk-thm-chow-projective`; the existing node and docstring
cite the older `sec-curve-estimates/sk-thm-br` snapshot. Both texts give the same
closed-immersion argument; the existing DAG has already corrected the blueprint's
unqualified finite-type assertion by requiring quasi-compactness.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
