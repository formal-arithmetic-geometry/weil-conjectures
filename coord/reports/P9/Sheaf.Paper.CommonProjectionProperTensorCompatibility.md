## What changed

Filled `WeilConjectures.commonProjectionProperTensorCompatibility` in
`Sheaf.Paper.CommonProjectionProperTensorCompatibility`, preserving its statement and docstring.
The proof chooses the existing `commonProjectionTensorComparison H E₀` once for both squares.
The compact-support square pastes `commonProjectionProperFactor` and
`commonProjectionOpenFactor` with `projection_preserved_of_factors`.
For the proper square, private proved helpers normalize the specified proper projection to its
pull/direct adjunction mate, identify the coefficient adjunction's mate with its right comparison
using its counit equation, and apply the source library's proved
`Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv` to
`commonProjectionPullbackTensorCompatibility` at the identity-open proper square.

Added only proof imports of `CommonProjectionProperFactor`, `CommonProjectionOpenFactor`, and
`CommonProjectionPullbackTensorCompatibility`. Updated the item's DAG proof and proof dependencies
to record these existing declarations. No shared definitions, public imports, or other modules
were changed; no change record or consumer adaptation is required.

Validation: `lcompile.py` compiled the final module successfully in 33.0 seconds with no warnings.
The original theorem signature matches verbatim, and the delivered module contains zero `sorry`
tokens. All three proof imports are used.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.commonProjectionProperTensorCompatibility`
(node `lem-sf-common-projection-proper-tensor-compatibility`): 1 of 1.
The five private helpers are proved. No holes remain in the item, and no holes or split-off
statements were added anywhere. This is a proof from existing dependencies, not a decomposition.
The imported `commonProjectionPullbackTensorCompatibility` is an existing unfinished dependency;
its finite-representative calculation remains assigned to its own node and is not claimed here.

## No longer needed

No imports were removed and no modules are withdrawn. The compact-support-only existential
`commonProjectionTensorCompatibility` is not used: its existential witness cannot supply the
proper square for an arbitrary tensorator. Instead the proof uses the same canonical tensorator
and the already stated proper/open factor equations directly. Its module remains independently
needed elsewhere; this delivery claims no global pruning.

The item's direct proof no longer redoes the constructions in
`def-weil-derived-pullback-tensor-hom`, `def-weil-algebraically-closed-coefficients`, or
`def-pur-completed-pullback-tensor-comparison`. They remain transitively needed by the canonical
tensorator and tensor/pullback square, so they are not globally pruned. The original statement
dependencies are preserved. The unit route through proper/open mates is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan describes constructing and checking the canonical
tensorator from finite representatives, but the current library already exposes that tensorator,
the proper/open factor equations, and the strictly smaller tensor/pullback square. Reusing those
interfaces closes this item's hole without another renamed compatibility obligation. The proper
square is proved independently by adjunction transposition, not inferred from compact-support
coherence. The proof imposes no extra condition on zero inputs, empty schemes, or identity opens.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
