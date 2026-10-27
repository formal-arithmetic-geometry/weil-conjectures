## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralFinitePullback_onGood`
in `Sheaf.SixFunctors.IntegralFinitePullbackNormalization` from the existing
`integralReductionPullFiniteSquare`. The two statements use different finite
geometric pullback presentations. Proved private helpers showing that deriving
the ordinary adjoint-uniqueness comparison equals the uniqueness comparison of
the derived adjunctions, then used naturality to identify the scalar comparisons.
Equality of the forward composite isomorphisms gives the required inverse equation.

Added proof-only imports of `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare`
and `Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition`.
The original public import and public theorem signature stay unchanged. Updated
the item's node proof, proof dependencies and proof origin to describe this route.

Validation: the server compiler accepted the complete module without warnings in
7.7 seconds. Static checks verified the unchanged public signature and imports,
zero local holes, line lengths, and the allowed node-field changes.

## Proved and sorry left

Closed one of one original holes:
`WeilConjectures.IntegralSystemRealization.integralFinitePullback_onGood`
(node `lem-sf-integral-finite-pullback-normalization`). Zero holes remain in the
item and zero holes are added. No split-off statement or module is introduced.

The proof uses the pre-existing named theorem
`WeilConjectures.IntegralSystemRealization.integralReductionPullFiniteSquare`
(node `lem-sf-integral-reduction-pull-finite-square`), whose proof currently contains
`sorry`. This delivery closes the duplicate local obligation from that existing
statement; it does not claim a sorry-free transitive proof of the coefficient calculus.

## No longer needed

The item's direct proof dependency
`lem-sf-scalar-pull-coefficient-complex-normalization`
(`Sheaf.Paper.ScalarPullCoefficientComplexNormalization`) is unnecessary for this
route and is removed from this node's proof dependencies. Its module was not an
existing import of the item and is not withdrawn; other proofs may still need it.
The ordinary projection/tensor-generator and good-pullback calculation need not
be repeated here: they belong to the already stated finite square theorem.
No existing imports are removed and no modules are withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original node plan overlooked an existing arbitrary-object finite square in
`IntegralReductionPullFiniteSquare`. Once its finite pullback presentation is
identified with the derived adjoint presentation, taking the inverse specializes
that theorem to this item's equation. The needed identification is proved, not
assumed. Both the Lean import check and a traversal of the existing DAG found no
cycle through that dependency. The unit route is preserved. No statement,
definition, shared instance, attribute, or source-library file is changed.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
