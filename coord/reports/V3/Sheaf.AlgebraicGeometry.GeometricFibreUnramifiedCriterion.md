## What changed

Completed `AlgebraicGeometry.unramified_iff_unramified_geometric_fibres` in
`Sheaf.AlgebraicGeometry.GeometricFibreUnramifiedCriterion`, preserving its statement.
The proof follows all four existing DAG steps. Base-change stability gives the forward
implication. Pullback pasting identifies the geometric fibre with the base change of the
ordinary fibre; the algebraic-closure field extension is an fpqc singleton cover, so
`locallyOfFiniteType_and_openDiagonal_of_fpqcCover` descends unramifiedness. The
field-fibre decomposition then supplies the ordinary-fibre criterion. The final glue
inverts the coproduct isomorphism and checks its structure map on each coproduct summand.

Validation: `lcompile.py` compiled the completed module successfully in 4.1 seconds.
The theorem signature is byte-for-byte unchanged and every Lean line is at most 100 characters.

Added proof imports of Mathlib's formally unramified morphisms and pullback
pasting API. No public imports, signatures, definitions, or other modules changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.unramified_iff_unramified_geometric_fibres`
(node `lem-trf-geometric-fibre-unramified-criterion`).

Item holes: 1 before, 0 after. Added holes: 0. Split-off statements: 0.
The proof uses the existing statements
`AlgebraicGeometry.unramified_iff_exists_iso_coproduct_spec_finite_separable` and
`AlgebraicGeometry.unramified_of_ordinary_fibre_coproduct_finite_separable`, whose existing
proof holes are unchanged and belong to their separate modules.

## No longer needed

None. All existing proof imports and all declared mathematical dependencies are used.
No node, module, or unit step is bypassed, and no DAG route update is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The decomposition and ordinary-fibre criterion use opposite
orientations for the coproduct isomorphism and different presentations of its structure-map
compatibility; the proof explicitly bridges these equivalent formulations.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
