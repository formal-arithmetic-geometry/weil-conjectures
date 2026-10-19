## What changed

Proved `AlgebraicGeometry.finiteType_noetherianCover_dimension_geometricFibres` with its
signature unchanged. Two proved private helpers supply affine and global source dimension
bounds. A finite affine subcover proves the Noetherian source-cover clause; stalk maps prove
preservation of units. The existing proved theorem `topologicalKrullDim_pullback_le` bounds
all field-valued pullbacks by the source dimension, so the same natural bound works uniformly.
Updated the node's proof route and the declaration's proof explanation to match the Lean proof.
All original public imports remain public; all added imports are for proofs.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteType_noetherianCover_dimension_geometricFibres`
(node `lem-cbc-compactification-geometry-fibre-bound`). Added zero holes; no sorries remain.
The private helpers `affine_dimension_bound` and `finiteType_source_dimension_bound` are proved.
The resumed session rechecked the unchanged public signature. A fresh compile of the complete
source with an appended `#print axioms` check passed against the current server snapshot in
2.3 seconds and reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the theorem.
The retained attempt's two unsubmitted split-offs were discarded after replacing their route;
no new public theorem or node is delivered for them.

## No longer needed

Removed original proof imports `Mathlib.RingTheory.TensorProduct.Basic`,
`Mathlib.RingTheory.TensorProduct.Maps`, `Mathlib.LinearAlgebra.TensorProduct.Tower`,
and `Mathlib.Algebra.MvPolynomial.Basic`.
The proof no longer needs `lem-weil-pbc-open-fibre-product`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-algebra-tensor-pushout-universal-property`, `def-weil-module-base-change`,
or `def-weil-pbc-mv-polynomial-ring` as direct dependencies: it uses the existing field-pullback
comparison instead of repeating the tensor-generator computation. `def-weil-affine-spectrum`
remains a statement dependency, but is no longer separately needed in the proof route.
The retained attempt's added imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`WeilConjectures.Mathlib.RingTheory.FiniteStability` are also unnecessary and not delivered.
No existing project module is withdrawn, and no blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt's affine pullback signature required unstated algebra instances and its
private reduction attempted to apply a canonical pullback statement to an arbitrary pullback
without transporting the square. That unsubmitted route is removed entirely.
The original plan was valid but longer than necessary: the proved source-library field-pullback
dimension theorem avoids a second finite-cover argument for geometric fibres.
The additional closed source tool is `topologicalKrullDim_pullback_le`, which uses the closed
source field-extension realization of `lem-pc-dim-base-change`. The unit has no separate
field-extension comparison; this use does not replace its compact-support route. The unit
record `sk-prop-sf-cbc` has no realized statement or proof-step node for this auxiliary item.
Empty schemes and zero rings are included: finite subcover maxima default to zero, and all
bounds live in `WithBot ℕ∞`, so bottom dimension satisfies them. No hypothesis, universe,
visibility or conclusion of the original theorem changed.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
