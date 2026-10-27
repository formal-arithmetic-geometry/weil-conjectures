## What changed

The item theorem now combines two named normalization lemmas, one for the
whole-system pullback and one for whole-system scalar extension.  The two
lemmas are in `Sheaf.Paper.TransportedReductionPullbackNormalized` and
`Sheaf.Paper.TransportedReductionScalarNormalized`; each has the proof plan
and a single named `sorry` for the corresponding transport/comparison step.
The item imports these modules privately and proves its conjunction by applying
both lemmas pointwise.

## Proved and sorry left

`WeilConjectures.transportedReductionSystems_normalized` is proved from the two
strictly smaller conjunct lemmas.  The split-off declarations
`WeilConjectures.transportedReductionSystems_pullback_normalized` and
`WeilConjectures.transportedReductionSystems_scalar_normalized` remain as
`sorry`; they are the inverse-image and scalar-extension transport statements,
respectively, with their own DAG nodes.

## No longer needed

The item proof no longer directly uses the old proof dependencies
`lem-coef-semilinear-derived-sections`,
`lem-pur-coefficient-extension-reduction-model`,
`lem-pur-system-normalized-tensor-closure`, and
`prop-weil-pbc-proetale-constant-exact`; those are retained as dependencies of
the corresponding split-off nodes.  The statement import
`Sheaf.Paper.IntegralComparisonSequenceSystems` remains needed.

## Where the brief, the DAG or earlier work was wrong

No statement or mathematical route in the brief was changed.  The existing
module's two proof steps were not available as Lean declarations specialized to
these actual whole-system functors, so the proof was decomposed into the two
proper conjunct statements rather than leaving an anonymous partial proof.

## New nodes

`stage3-trf-transported-pullback-normalized` records the inverse-image
normalization step and its named theorem.

`stage3-trf-transported-scalar-normalized` records the scalar-extension
normalization step and its named theorem.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
