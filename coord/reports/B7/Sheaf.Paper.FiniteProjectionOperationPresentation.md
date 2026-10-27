## What changed

Replaced the hole in `WeilConjectures.finiteProjection_operationPresentation` by an
explicit composition of arrow isomorphisms. The intrinsic compactification projection
is its proper counit factor followed by an isomorphism. The fixed-scalar projection
has the same form. The proof removes the first open tail, compares the proper factors,
transports the extension-by-zero input by the existing `finiteOpenIso`, inserts the
second open tail, and cancels the operation-side source/target conjugation.

Added `Sheaf.Paper.FiniteScalarProperProjectionPresentation`, with the actual proper
counit transpose exposed as `finiteScalarProperProjection`, and one remaining
comparison theorem. This is a strictly smaller argument: it has no open immersion,
compactification, support functor, operation datum or restricted input domains. The
parent proof supplies all the open and operation-coordinate assembly in Lean.

Updated the item's proof plan and added the node for the proper-factor comparison.
Existing declaration signatures and public imports are unchanged. No existing module
besides the item was edited. A private assembly lemma keeps the coefficient ring
abstract during elaboration. Declaration-local settings select the standard
derived-category instance; no attribute or instance change is exported.

## Proved and sorry left

Decomposition, not a net hole closure: the original single hole in
`WeilConjectures.finiteProjection_operationPresentation` is replaced by a complete
proof using one new strictly smaller comparison statement. One hole closed, one added;
net zero. The seven private assembly helpers are proved, and the new proper projection
definition has no hole. The full assembly compiled successfully (14.8 seconds);
profiling options were removed before delivery.

The only remaining `sorry` in this delivery is
`WeilConjectures.finiteScalarProperProjection_presentation`
(node `lem-sf-finite-scalar-proper-projection-presentation`). Its source and complete
proof in words are in its docstring and node. It asserts compatibility of the two
proper counit factors, without asserting their invertibility.

## No longer needed

No original public import is removed: both are used in the item's statement.
No module is withdrawn or globally pruned. The new proper-factor module imports
the tensor and realization APIs directly.

The old plan's comparison of the specified open projection transposes, and its
compatibility with the specified pullback compositor, are unnecessary for the stated
`Nonempty` arrow-isomorphism conclusion. Both tails are already isomorphisms, so
postcomposition supplies the needed arrow isomorphisms directly. The former direct dependency
`lem-sfb-constant-module-derived-projection-identification`
(`Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification`) remains in the
new proper-factor node's plan. It is not claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The old plan proved more than the Lean statement requested: compatibility through
prescribed endpoint comparisons. The statement asks for the existence of an arrow
isomorphism. Removing and reinserting the open tails therefore avoids their
normalization square without weakening or changing the statement.

The general constant-module derived projection theorem requires explicit geometric
and tensor comparison data. It does not immediately specialize to the two actual
pro-etale tensor presentations in the item. The remaining node isolates exactly this
proper-factor specialization, while the parent now proves the other steps.

Edge cases of the new statement were checked mathematically: zero inputs, empty
schemes and the zero coefficient ring use the same equivalences and adjunctions.
There is no constructibility or finite-Tor hypothesis to fail for an unbounded input.
The original hypotheses, including the bounded constructible first input without a
finite-Tor assumption, remain unchanged.

## New nodes

`lem-sf-finite-scalar-proper-projection-presentation` realizes the proper counit
transpose step of the existing plan in its own module. It compares the intrinsic
proper projection, in arbitrary flat K-flat tensor models over a finite ring, with
the realization of the fixed-scalar proper projection. It does not restate the
compactification presentation theorem: the latter is now assembled using this proper
comparison and the existing open extension and endpoint isomorphisms.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
