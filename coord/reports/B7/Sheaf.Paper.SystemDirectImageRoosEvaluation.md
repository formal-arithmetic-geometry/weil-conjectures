## What changed

Replaced the proof hole in `WeilConjectures.systemDirectImage_roosEvaluation`
without changing its statement or public imports. The proof now factors both
actual projections through the finite scalar adjunction. For each level it
constructs the required comparison as the inverse of the total-limit projection
adjunct, followed by scalar extension of the given `e`, followed by the Roos
projection adjunct. Adjunction naturality proves the requested projection
equation for the given arbitrary `e`.

Added `Sheaf.Paper.SfDirectImageRoosFiniteReduction`, proving
`sfDirectImageRoos_finiteReduction` with no holes. It completes the input using
the reduction-limit adjunction, proves that the completion unit induces
isomorphisms on all finite reductions, transports the specified Roos triangle,
and applies the existing complete-input direct-image theorem. In particular,
this step does not assume that the original input is complete.

Added `Sheaf.Paper.SystemDirectImageReductionNormalized` for the remaining
normalization step. The main module imports these two modules and unrestricted
normalized reconstruction privately. Only the item, its own node, and the two
new modules and their nodes are changed. No existing definition, instance,
attribute, declaration signature or public import is changed.

## Proved and sorry left

Closed the original local hole in
`WeilConjectures.systemDirectImage_roosEvaluation` (one of one original holes).
Its proof is complete from the named dependencies.

Also proved `WeilConjectures.sfDirectImageRoos_finiteReduction`, node
`lem-weil-sf-direct-image-roos-finite-reduction`, with zero holes.

Added one hole, exactly the public theorem
`WeilConjectures.systemDirectImage_reduction_normalized`, node
`lem-weil-system-direct-image-reduction-normalized`. It states only that the
whole-system direct image of a reduction is normalized. It has no Roos object,
no total-limit isomorphism `e`, and no comparison with Roos projections. Its
source and complete proof in words are in its docstring and node. It is a
strictly smaller transition-property step, not the original assertion renamed.

Thus this packet decomposes the original hole into one lower hole; it claims no
net decrease in holes. The finite-reduction transport and the final adjunction
cancellation are fully proved. Existing dependencies may still contain their
own previously registered holes.

## No longer needed

The item proof no longer directly needs
`stage3-pur-canonical-tower-roos-comparison`
(`Sheaf.Paper.CoefficientConstantTowerRoosComparison`). Normalized reconstruction
and the two projection adjuncts replace that route. This is a pruning of the
item proof route only; no global withdrawal of that node or module is claimed.

The former direct dependency `lem-trf-direct-image-restriction-transition` is
needed only in the proof plan of the lower normalization statement, and remains
recorded there. `lem-coef-derived-system-evaluation-calculus` remains used.
No existing public import is removed, and no source-library declaration or
module is withdrawn. In particular the existence theorem is still used by the
parent presentation theorem.

## Where the brief, the DAG or earlier work was wrong

The old proof sketch passed from a canonical comparison to a projection equation
for an arbitrary isomorphism `e` without supplying the transport argument. A
chosen object isomorphism need not itself preserve the specified Roos
projections. The new proof constructs new finite isomorphisms using `e` and
proves their actual projection equations by adjunction naturality.

The normalization step still needs the coherent derived evaluation and quotient
transition comparisons, not just a collection of objectwise finite evaluation
isomorphisms. The new lower node records that precise remaining obligation.
No false statement or definition repair is asserted.

The existing DAG also has an aggregate-node cycle already present before this
packet: the item has `def-weil-derived-direct-image` as a statement dependency;
that definition node depends on `lem-sf-integral-pullback-linear-adjunction`,
which depends on `def-weil-system-operation-exchange-realization`, which depends
on the parent Roos presentation and hence this item. This reflects the broad
source-module attachment of the definition node, not a Lean import cycle. Those
other nodes are unchanged; the new modules compile in import order.

## New nodes

`lem-weil-sf-direct-image-roos-finite-reduction` realizes the proved arbitrary-input
finite-reduction theorem in `Sheaf.Paper.SfDirectImageRoosFiniteReduction`.
Its proof uses normalized reconstruction, naturality of the finite direct-image
tower, transport of a distinguished Roos triangle, and the complete-input
reduction theorem.

`lem-weil-system-direct-image-reduction-normalized` realizes the one remaining
normalization statement in `Sheaf.Paper.SystemDirectImageReductionNormalized`.
The proof plan specifies a single sequence-site K-injective resolution, the
section-normalized finite evaluation and quotient comparisons, the perfect
quotient projection formula, and scalar-extension associativity. Edge cases
include identity quotients, level zero, zero input and empty schemes.

There are no change records because no existing interface is changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SfDirectImageRoosFiniteReduction": "d30bac1d5efb0ddabf859b633158c8aaff4588f0", "Sheaf.Paper.SystemDirectImageReductionNormalized": "ac8dff61566d1362f289ebd62b38b88f5f4f341d", "Sheaf.Paper.SystemDirectImageRoosEvaluation": "b927bb4fd33c7aadcb4e845d6ca776210ff7c5e8"}, "results": {}, "time": "2026-10-28T12:11:28+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
