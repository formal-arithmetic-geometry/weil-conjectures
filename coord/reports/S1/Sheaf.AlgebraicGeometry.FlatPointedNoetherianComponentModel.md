## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.FlatPointedNoetherianComponentModel` with a complete Lean proof
from the declared dependencies. The public statement and public imports are unchanged.
Three proved private helpers specialize eventual flatness to the affine approximation,
construct a flat Noetherian model with its section, and compare iterated geometric fibres.
The section construction follows the already proved source-library constructions in
`SectionNoetherianDescent` and `SmoothSectionComponentNoetherianModelData`, with eventual
flatness replacing eventual smoothness. These modules are not imported or changed.

The proof advances to a flat stage before descending the section, so later pullback
preserves flatness. Reducedness is transported through the model isomorphism and the
existing geometric-reduced-fibre locus theorem. Two applications of the proved
section-component cartesian lemma finish the locus equality. The node proof now records
this order and the actual comparison argument. No unit route is changed.

Validation: `lcompile.py` accepted the final module with exit code 0, no errors or
warnings, in 7.5 seconds. Its public signature was compared verbatim with the shared
source and is unchanged. The module contains zero `sorry` tokens and every line is at
most 100 characters. All changes are confined to the assigned module and its node.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_flat_pointed_noetherian_component_model`
(node `lem-trf-flat-pointed-noetherian-component-model`).

Added 0 holes and split off 0 statements. There are no `sorry` declarations left in the
item or added by this delivery. The proof uses the existing declared dependency
`AlgebraicGeometry.geometricReduced_fibre_locus_baseChange`, which remains a theorem with
`sorry` in its own unchanged module (node
`lem-trf-geometric-reduced-fibre-locus-base-change`); no transitive axiom-free claim is made.

## No longer needed

The separate Mathlib-leaf dependency `lem-weil-pbc-lft-pointwise-criterion` is unnecessary:
Mathlib's `LocallyOfFinitePresentation` directly supplies `LocallyOfFiniteType` by its
finite-presentation-to-finite-type instance. Removed this node from the proof dependencies.
No imports or project modules are removed; every existing proof import is used.
All other declared proof dependencies remain used, and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's section-first, flatness-second
ordering is valid, but the existing source-library section-descent construction is more
convenient with flatness descended first. Its morphism descent is used in the
source-equal-to-the-base formulation `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
The inherited declaration docstring describes the original valid ordering; the updated
DAG and actual proof record the equivalent ordering used here. No shared definitions,
source-library declarations, or other consumers were changed.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
