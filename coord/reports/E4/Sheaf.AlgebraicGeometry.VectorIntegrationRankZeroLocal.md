## What changed

Reduced `AlgebraicGeometry.Etale.vectorIntegration_rankZero_localIdentity` in the assigned
module, preserving its full statement. Added only private proved helpers and private proof
imports for affine exchange pasting and the isolated coefficient normalization.

The proof derives compatibility of identity comparisons from composition: naturality,
cancellation of an invertible exchange, and faithfulness of a functor isomorphic to the
identity suffice. Applied to bounded-below inclusion, this identifies the zero-stage compact
comparison with the specified unbounded identity comparison. Applied to identity-projection
exchange, it gives the corresponding base-change normalization. The chart coefficient
calculation is reduced to a new public theorem, with its complete proof in words using
the actual pullback compositors and their unit laws. Precomposing by the
pullback of `b.hom`, exchange pasting combines these calculations into the requested equation.
The zero affine counit is evaluated from its literal identity adjunction.

Validation: the assigned module compiled through lcompile.py in 23.0 seconds after
normalizing the zero-stage identity objects; the new coefficient module compiled in
22.6 seconds. No source-library file was changed.

Updated the existing node's proof, proof dependencies, and proof origin to record this
argument and its use of `lem-amb-affine-linear-exchange-coherence`. No source-library file,
public declaration type, public import, definition, instance, or target was changed.

Search: LeanFinder for identity counit/rank-zero local trace found unrelated topological
vector-bundle results. Loogle found `Adjunction.id` and `Adjunction.id_counit`, constituent
identity-adjunction facts only. The remote grep query returned no results. Local `rg` of
both library roots found the existing exchange-pasting theorem and the unbounded composition,
unit, and bounded-below comparison theorems used here. The coefficient normalization step is isolated below as a strictly smaller obligation.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.vectorIntegration_rankZero_localIdentity`
(node `lem-pur-vector-integration-rank-zero-local`).

Holes closed: 1. Holes added: 1. Split off: 1. This is a decomposition, not a net proof gain.
The one remaining hole is
`AlgebraicGeometry.Etale.vectorIntegration_chartCoefficient_zero`, in the new module
`Sheaf.AlgebraicGeometry.VectorIntegrationChartCoefficientZero`. It is only the coefficient
comparison calculation and contains no compact-support exchange or counit. All private
helpers are proved; the assigned theorem has a complete proof from the stated dependencies.

## No longer needed

No imports were removed, and no nodes or modules are withdrawn or pruned. The original
public imports are required by the unchanged statement. Both added private imports are used by the proof. The new coefficient node replaces
the former direct coefficient calculation in the proof route. The tower node remains
needed below that coefficient node.

The former plan's separate identification of the inverse frame using `zero_isIso` is
unnecessary: the existing chart square directly gives `chart ≫ π = V.ι` at rank zero.
The vector-geometry node remains needed for its specified identity-bundle square.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original plan was mathematically
sound but omitted a short algebraic route to the two identity normalizations. The parent
proof obtains both from the existing composition and unit equations, avoiding additional
compactification or injective-resolution calculations. The statement and unit route stay
unchanged. The argument does not assume a nonempty open or a nonzero coefficient ring.

## New nodes

`lem-pur-vector-integration-chart-coefficient-zero`, realized by
`AlgebraicGeometry.Etale.vectorIntegration_chartCoefficient_zero` in
`Sheaf.AlgebraicGeometry.VectorIntegrationChartCoefficientZero`. It states only the
rank-zero coefficient comparison after the chart/projection compositor. Its complete
proof in words is in its docstring. The arguments for identity exchange and zero compact
comparison are proved in the assigned module and are not restated as obligations.

The remaining mathematical obligation is the normalization of the actual chart coefficient
through equality transport between the pullback compositors. Its algebraic argument is
recorded completely in the docstring. The implemented abstract categorical calculation
compiled in 15.5 seconds, and a zero-stage expansion equation compiled by rfl in 8.3
seconds. Connecting the actual chart coefficient to that abstract calculation remained
unfinished: Lean attempted expensive definitional conversion when instantiating the
compositor at the zero-stage chart. These exploratory private helpers and the diagnostic
probe are omitted from the delivery; only the needed coefficient statement remains.
The file limit and definitions are unchanged.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
