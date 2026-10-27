## What changed

Completed `AlgebraicGeometry.quasiFiniteAtPoint_of_dominant_integral_curves` in
`Sheaf.AlgebraicGeometry.DominantIntegralCurveQuasiFinite`, preserving its complete
signature and all public imports. Updated its docstring and DAG proof to the actual argument.

For each curve, points other than the generic point are closed, using the existing
`IsOpen.isClosed_singleton_of_mem_compl`. Dominance sends generic point to generic point.
The target is Jacobson, so Mathlib's `Scheme.Hom.closePoints_subset_preimage_closedPoints`
sends closed points to closed points. The generic fibre is contained in the source generic
singleton; every other fibre is a closed subset of closed points and is finite by
`IsClosed.finite_of_finiteType_over_field_of_closed_points`. Apply
`Scheme.Hom.discreteTopology_fiber_and_quasiFiniteAt` and the already proved
`Scheme.Hom.isQuasiFiniteAtPoint_iff_quasiFiniteAt` comparison.

Added private proof imports of `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
`WeilConjectures.Mathlib.Topology.KrullDimension`, and
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`.
No definitions or statements changed; no consumer adaptations are needed.
The unit and chapter route is preserved. Only the assigned module and its node are changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.quasiFiniteAtPoint_of_dominant_integral_curves`
(node `lem-trf-birational-curve-quasifinite`).
Added 0 holes, split off 0 statements, and left 0 holes in the delivery.
All directly used ingredient declarations are already proved.
The finite generic extension, separatedness and over-base compatibility hypotheses are
retained verbatim even though this argument does not need them.

Validation: server single-file compilation through `lcompile.py`; delivery preflight
provides the final compilation and axiom checks. Import-direction checks pass for both
new WeilConjectures proof imports. The point and fibre arguments include empty fibres;
inseparable morphisms need no special treatment, and constant maps are excluded by dominance.

## No longer needed

Removed the private import `Sheaf.AlgebraicGeometry.ClosedPointField` and the proof
dependencies `lem-kun-closed-point-field` and `def-weil-residue-field`: Mathlib's direct
closed-point image theorem replaces that calculation. Removed the corresponding obsolete
`tool_uses` entry for `lem-kun-closed-point-field`.
These declarations may still serve other consumers; no module is withdrawn.
The generic point, dimension, finite closed subset and finite-fibre dependencies remain.
Added the already existing node `lem-sc-dim-one-point-outside-open-closed` to Step 1's
uses and recorded the quasi-finiteness comparison under `pqf-def-quasifinite`.
No additional unused imports were retained.

## Where the brief, the DAG or earlier work was wrong

The original planned residue-field argument was correct but longer than needed: Mathlib
already proves closed-point preservation for locally finite type maps to Jacobson targets.
The finite-fibre dependency returns Mathlib `QuasiFiniteAt`; an explicit comparison to
Stacks `IsQuasiFiniteAtPoint` is required, and is supplied by the existing comparison module.
The mathematical statement and unit route are unchanged.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
