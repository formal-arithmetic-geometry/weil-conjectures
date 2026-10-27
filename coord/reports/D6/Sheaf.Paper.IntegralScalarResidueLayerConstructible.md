## What changed

Replaced the original sorry in `WeilConjectures.integralScalarResidueLayer_constructible`
by an assembly proof of the finite-local-model argument. The existing public signature and
public imports are unchanged. Proved private helpers give the exponent-one quotient-field
structures, preservation of finite local constancy and constructibility under restriction
of scalars, and the natural comparison between fixed-module and ringed-module restriction.
The proof computes source residue homology on the given K-flat complex, applies the
privately proved exact finite-field scalar extension using the existing local tensor model,
restricts the same finite models,
and transports constructibility along homology isomorphisms.

The only split is the derived tensor comparison in the new module
`Sheaf.Paper.IntegralScalarResidueLayerTensorComparison`. It states the actual derived
isomorphism between the uniformizer-layer tensor and the two-stage residue tensor.
It has no constructibility hypothesis or conclusion, no interval, and no K-flat hypothesis.
Its source is the arithmetic/associativity step of the original plan, and its docstring
specifies both balanced maps, the cancellation argument and the coefficient compatibility.
This separates a genuine tensor computation from the finite-model preservation proved here.

Validation: the comparison module compiled in 43.5 seconds. The first assembly proof
compiled in 18.2 seconds; the final version also checks the import direction and privately
reproves the cyclic packaged scalar-extension clauses. Profiling options were removed
after resolving universe inference in restriction of scalars. Final checks are reported
by the delivery tool.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralScalarResidueLayer_constructible`
(node `lem-sf-integral-scalar-residue-layer-constructible`).

Added one hole:
`WeilConjectures.integralScalarResidueLayerTensorComparison`
(node `lem-sf-integral-scalar-residue-layer-tensor-comparison`).

Thus this is a decomposition, with one original hole closed and one comparison hole added,
net zero holes. There are zero textual sorries in the item module, one in the new module,
and none in any private helper or definition. No assertion of a complete proof of the
remaining arithmetic/tensor comparison is made.

## No longer needed

No library module is withdrawn and no existing public import is removed.
`lem-sf-finite-field-sheaf-scalar-extension` is not used as a dependency: its proof import
of the upstream scalar-extension library reaches this item through the projection formula.
The needed exactness and finite-model clauses are proved privately from flatness, tensor
sheafification, adjoint uniqueness and `lem-sf-finite-field-local-tensor-model`. The upstream
projection-formula restriction/pullback comparison is likewise replaced by a direct
conjugate of the coextension/direct-image identity; the restriction/coextension adjunction
is itself constructed by restricting the ordinary module adjunction to sheaves. Neither
upstream module is changed. The direct
constructibility argument does not use the interval or the cohomological-support
hypothesis; both remain verbatim in the public statement. Consequently
`def-weil-cohomological-support` is no longer a direct proof dependency, but remains a
statement dependency and is still required by the separate vanishing clause.
The general derived-change-of-rings argument and arithmetic layer identification remain
needed by the new comparison node. All other original dependencies remain needed either
directly or there. No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

Delivery detected an import cycle through the packaged finite-field scalar-extension
theorem. Replacing its use by the private flatness and local-model argument, and the
restriction/pullback comparison by the coextension conjugate, removes those cyclic imports.

The original dependencies do not state the B-linear identification of the actual layer
tensor complex with restriction of the residue scalar-extension complex. Finite-field
scalar extension gives exactness and preservation of finite models once that comparison
is available; the DVR theorem gives the valuation data, rather than the sheaf comparison.
The new node records exactly this missing comparison instead of repeating constructibility
under another name. The existing item node's blueprint ancestry points at its immediate
parent; the blueprint ancestor tool returned None. The new node follows the recorded
ancestry of the residue-layers and finite-level-bounds nodes to
`def-weil-rationalization-karoubi`. The current blueprint's scalar-extension proof step (4)
and the local Stacks tensor-product and constructible-Serre sources were read.

The new comparison was checked mathematically at n=0, j=0, the last nonzero layer j=n,
ramified field inclusions, the identity inclusion, zero complexes and the empty scheme.
It uses cancellation only in the valuation domain before passage to finite quotients.
The inverse balanced map retains the source residue scalar and the forward map retains
the target coefficient; the restriction preserves the underlying finite sets.

## New nodes

`lem-sf-integral-scalar-residue-layer-tensor-comparison` is the derived-category comparison
of the two explicitly specified tensor constructions, independent of constructibility,
bounds and K-flatness. Its only sorry is the entire proof of the named public theorem.
The parent takes homology of this comparison and performs the finite-model preservation
argument in Lean. No change record is needed: no existing statement, definition, instance,
attribute or public import has changed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
