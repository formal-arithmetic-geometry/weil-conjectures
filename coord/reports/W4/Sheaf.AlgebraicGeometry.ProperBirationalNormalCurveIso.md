## What changed

Filled the proof of `AlgebraicGeometry.isIso_of_isProper_birational_normal_curve`
in `Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso`, preserving its statement,
docstring and imports.

The proof follows the existing two-step DAG route. It obtains `IsFinite p` from
`AlgebraicGeometry.isFinite_of_isProper_birational_curve`, supplying the dimension-one
fields of the two `IsIntegralCurve` instances. Continuity and dense range identify the
image of the generic point with the target generic point. Composing the assumed
bijective stalk map with the inverse stalk-congruence isomorphism gives the transported
function-field bijection required by
`AlgebraicGeometry.isIso_of_finite_birational_normal`, which concludes the proof.

The source statements were checked against Stacks varieties.tex,
`lemma-finite-in-codim-1` (0AB7), and morphisms.tex,
`lemma-finite-birational-over-normal` (0AB1). Searches of Mathlib and both library roots
found no shorter theorem matching the complete statement.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.isIso_of_isProper_birational_normal_curve`
(node `lem-trf-proper-birational-normal-curve-iso`).

No `sorry` remains in the item module. No holes were added and no statements were
split off. The final module compiled cleanly through `lcompile.py` (exit 0; 5.7 s).
The proof uses the existing, still-unproved dependency declarations
`AlgebraicGeometry.isFinite_of_isProper_birational_curve` and
`AlgebraicGeometry.isIso_of_finite_birational_normal`; their modules are unchanged.
This delivery closes the assigned hole from the declared dependencies, rather than
claiming the transitive dependency chain is axiom-free.

## No longer needed

None. Both declared proof dependencies and both corresponding proof imports are used.
All public imports support the existing statement interface. No nodes or modules are
pruned, and the DAG's proof route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The two dependency statements fit after the
explicit generic-point transport; no statement or definition repair is necessary.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
