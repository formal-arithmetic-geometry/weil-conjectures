## What changed

`Sheaf.Paper.NormalizedIntegralScalarCoherence` now proves the three unchanged
compatibility equations by transposing the actual lambda/mu square under the
reduction/realization adjunction. Private, fully proved categorical helpers paste
unit and tower squares and cancel the common counit coordinates. The scheme
identity follows from the quotient mixed-composition equation and geometric
unit laws; it uses no new normalization assumption.

`Sheaf.Paper.IntegralScalarCounitNormalization` isolates the normalization of
scalar realization counits under multiplication and associativity. It involves
only coefficient extension on one scheme, with no scheme morphism and no mixed
comparison. Its two equations are the normalization input to the actual pasting
argument, rather than any clause of the item renamed. No existing declaration signature, definition, public import or consumer is
changed. Local proof elaboration uses the same instance exclusions already used
by the comparison-system modules.

## Proved and sorry left

The original hole in `WeilConjectures.normalizedIntegralScalarCoherence` is
closed by a complete Lean proof from named dependencies. One new hole is added:
`WeilConjectures.integralScalarCounitNormalization`, node
`lem-trf-integral-scalar-counit-normalization`. The assigned module has zero remaining holes; the delivery contains exactly
one `sorry`, in that new public theorem. This is a decomposition (one closed, one added), not a net hole reduction.
The geometric identity clause and the generic unit/tower pasting and mate
calculations are proved without this new hole; the scalar clauses use it.

Validation: the main module compiled cleanly in 43.5 seconds and the new
normalization module compiled cleanly in 14.1 seconds through `lcompile.py`.
The original theorem signature is textually unchanged. Temporary model-bridge
experiments are excluded from the delivery.

## No longer needed

The item no longer depends on node `lem-trf-counit-realization-substitution`
(module `Sheaf.TraceFormula.CounitRealizationSubstitution`). Its full word calculus,
normalization of all intermediate systems, and word invertibility are unnecessary
here: the given system already supplies the effective counits on the specific
constructible inputs that occur, and the actual reconstruction unit detects the
required morphism equalities. This is a dependency removed from this item's
route; other consumers may still need it. The original module had only its
statement import, which is retained. The two proof imports are quotient mixed
coherence and the new scalar counit normalization; the constructible restriction
implementation is imported privately for the effectivity and completeness instances. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's single prose step hid the distinction between the ordinary finite-free
scalar model used in `integralComparisonScalarUnit` and
`integralComparisonScalarAssociator` and the universal derived tensor model used
in `scalarModelUnit` and `scalarModelAssociativity`. The models are canonically
identified by their tensor-generator and counit normalizations, but they are not
definitionally the same. The new node isolates precisely that scalar normalization
and its adjoint transposition.

The existing proved model identification in
`Sheaf.Paper.IsomorphismComparisonScalarExtension` cannot be imported: that module
imports `IntegralPullbackComparisonRealization`, whose proof reaches this item.
The new node's proof describes the lower construction directly, rather than
introducing a circular dependency. The fixed unit route is unchanged.

The first preflight found a DAG cycle in the broad tensor/completion definition
citation `def-pod-scalar-completion-tensor-comparisons`, which also includes
completed tensor and pullback dependencies. The scalar-only normalized completion
node `lem-weil-normalized-scalar-completion` is the actual input needed here; its
statement and proof supply the specified completion comparison without that
unrelated tensor/pullback route. The corrected dependency closure does not reach
the assigned node. Lean imports and statements are unchanged by this correction.

## New nodes

`lem-trf-integral-scalar-counit-normalization`, in
`Sheaf.Paper.IntegralScalarCounitNormalization`, states the multiplication and
associator equations for the actual scalar realization counits. Its proof is the
scalar-model normalization part of the original argument, followed by adjunction
naturality and triangle identities. Edge cases checked: zero inputs, empty
schemes, equal fields, identity embeddings, and ramified extensions. No quotient
coefficient map is assumed flat, and no finite Tor-amplitude bound is added.

Change record: `coord/changes/S5-normalized-integral-scalar-proof-context.md`
records the proof context commands flagged by the conservative command-diff check.
They introduce no change to the existing public declaration or instances.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
