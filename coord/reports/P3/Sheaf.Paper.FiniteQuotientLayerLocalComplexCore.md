## What changed

Replaced the `sorry` proof of
`AlgebraicGeometry.Scheme.finiteQuotient_layer_local_complex_core` with a complete
Lean assembly of a concrete witness and four properties. The existing signature,
public imports and docstring are unchanged. Its sole added import is private:
`Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison`.

Added `Sheaf.Paper.FiniteQuotientLayerTensorComplex` with an actual ideal-power
quotient module, an equivalence with the kernel of the successive quotient ring map,
an additive tensor functor, and its termwise complex. Proved finiteness of the ideal
layer, finiteness of every successor-ring term, and both strict support bounds.
No data is chosen from an existence theorem and no definition contains `sorry`.

Added one residual comparison statement in its own module. Its conclusion concerns
the already constructed complex, with no existential witness, finiteness conclusion,
or support conclusion. It drops the lower support bound, finite-generation condition
on the input terms, compactness, and local Noetherian assumptions on the scheme.
The genuinely remaining work is identifying the actual sheaf-derived layer tensor
with this explicit algebraic tensor computation; it is documented using the displayed
balancing identity of Stacks 094I and the bounded-above projective calculation.

The initial module and dependency search found no direct existing comparison. Mathlib's
ideal-power quotient equivalence, quotient-map kernel identity, tensor functor, finite
tensor instance, and zero-object preservation supply the algebraic part. This is
below the unit level and keeps the unit route.

The original theorem and both new modules compiled individually in import order
through `lcompile.py`, within the per-file limit. The server queue listed the item
as `proof`, with one hole and no build-error record. The construction handles n=0,
zero layers, zero rings, and empty support intervals: no positive-rank, nontriviality,
nonempty-chart, or ordered-endpoint assumptions are used in its proofs. The remaining
comparison likewise states no such assumptions.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.finiteQuotient_layer_local_complex_core`
(node `lem-weil-pbc-finite-quotient-layer-local-complex-core`). Its proof now assembles
the following proved algebraic results with the residual comparison.

Proved without new holes:
- `AlgebraicGeometry.Scheme.finiteQuotientLayerModule_finite`;
- `AlgebraicGeometry.Scheme.finiteQuotientLayerTensorComplex_finite`;
- `AlgebraicGeometry.Scheme.finiteQuotientLayerTensorComplex_ge`;
- `AlgebraicGeometry.Scheme.finiteQuotientLayerTensorComplex_le`;
- `AlgebraicGeometry.Scheme.finiteQuotientLayerTensor_additive`.

The kernel equivalence and all construction bodies are also complete.

Added one hole, and this is the only `sorry` in the delivery:
`AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_homology_comparison`
(node `lem-weil-pbc-finite-quotient-layer-tensor-homology-comparison`, module
`Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison`).

This is a decomposition: one hole closed, one added, net zero holes removed.
The original item module now has zero holes; the new comparison module has one;
the new construction module has zero. The algebraic construction, kernel identification,
finiteness and interval bounds are genuinely proved, rather than moved to another
existence statement. The residual theorem is strictly the sheaf tensor calculation
for the fixed explicitly constructed complex.

## No longer needed

No existing import is removed, no module is withdrawn, and no module is claimed to
leave the targets' closure. The original direct proof-dependency list is replaced
by the construction and residual comparison nodes to match the Lean proof.
`lem-weil-pbc-site-derived-tensor-descent` and the coefficient-data nodes remain
transitive dependencies of the residual comparison; they are not globally pruned.
The algebraic construction uses no projectivity and no sheaf tensor descent.
The remaining comparison needs no lower support or finite-generation hypotheses.
No blueprint unit or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The prior node's single prose step joined a concrete
algebraic construction and a sheaf-derived balancing comparison without a directly
applicable comparison declaration. The delivery proves the entire algebraic part
and isolates the remaining calculation for that constructed witness. In particular,
this is not a claim that the sheaf-derived comparison has been completed.

## New nodes

`def-weil-pbc-finite-quotient-layer-tensor-complex` records the actual quotient module,
its quotient-map kernel equivalence, tensor functor and cochain complex, and the
proved bounds and finiteness API. Its source is the ideal layer in Stacks 094I.

`lem-weil-pbc-finite-quotient-layer-tensor-homology-comparison` records the remaining
chartwise homology comparison for this specified complex. Its proof in words is
in both the node and theorem docstring; it has one public theorem and one `sorry`.
It asks for neither existence nor support/finiteness of a model.

Change record: `coord/changes/P3-finite-quotient-layer-tensor-complex.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientLayerLocalComplexCore": "2032123f990a6b00b8a77331e03aa63bec899775", "Sheaf.Paper.FiniteQuotientLayerTensorComplex": "3b3171d0dfbe1cc802543cc08817a18e87ec46fb", "Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison": "790990869f7d23d3c401b2a97b6650c85f9cea76"}, "results": {}, "time": "2026-10-28T04:10:05+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
