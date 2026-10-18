## What changed

Proved `AlgebraicGeometry.curve_baseChange_smoothOfRelativeDimension_one` in
`Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne`, preserving its exact signature.
The curve's canonical topological dimension field and the proved source theorem
`smoothOfRelativeDimension_iff_topologicalKrullDim_eq` give relative dimension one for `f`.
The existing `smoothOfRelativeDimension_pullback_snd` instance gives the conclusion.
Updated the theorem docstring and the node's proof, dependencies and proof origin accordingly.
No unit statement or unit proof step is bypassed: this is a shorter proof of the same
auxiliary fact below `sk-prop-jacobian`.

Removed six unused direct imports; the two remaining public imports suffice.
The import interface record is
`coord/changes/D2-curve-base-change-relative-dimension-imports.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.curve_baseChange_smoothOfRelativeDimension_one`
(node `lem-sc-curve-base-change-relative-dimension-one`).
Added 0 holes, split off 0 statements, and left 0 holes in the delivered module.
The remote single-file compiler accepted the proof both before and after import pruning.
Both unchanged downstream modules, `HilbertToPicardMorphism` and
`HilbertToPicardSurjective`, also compile against the sandbox overlay.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
Thus this is a proof, not a decomposition onto further sorry declarations.

The arbitrary-base-change instance covers empty `T`; integrality of `C` supplies the
nonempty irreducible hypothesis of the dimension-comparison theorem. No projectivity,
properness, algebraic closedness, or extra hypothesis is introduced.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.Dimension`
- `Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic`
- `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.Mathlib.Topology.KrullDimension`

The last module remains available transitively through `Curve.SmoothProjective`;
removing a redundant direct import does not claim it disappears globally.
The retired Sheaf base-change wrapper only re-exports its source counterpart.
The proof needs only the categorical pullback, already available from the curve imports,
not the additional module/section/geometric-fibre conventions.

The original proof route's nodes `lem-sc-fibre-dimension-after-base-change`,
`lem-sc-dimension-locally-algebraic`, `lem-pc-scheme-dimension-local-rings`, and
`def-pc-scheme-fibre` are unnecessary for this proof: the existing smooth relative-dimension
comparison and stability instance replace the pointwise fibre computation.
`lem-pc-proper-base-change` is also unnecessary: the stronger relative-dimension stability
instance supplies the whole conclusion, including smoothness. Its obsolete top-level
`tool_uses` approval is withdrawn in the node copy.
The statement and proof retain the curve, smoothness and categorical base-change notions.
No module is withdrawn; these dependencies may still be needed by other items.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a separate fibre-identification/local-dimension argument even though its
own `mathlib_candidate` already pointed to the proved source-library dimension comparison.
The current canonical `IsIntegralCurve` stores `topologicalKrullDim C = 1` directly, so
there is no need to translate from `Scheme.dim` using the local-ring dimension theorem.
No mathematical statement required repair.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
