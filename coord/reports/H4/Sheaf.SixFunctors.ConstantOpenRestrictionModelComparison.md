## What changed

Replaced the hole in
`AlgebraicGeometry.Scheme.sfCbcOpenRestrictionModelComparison` by an explicit
comparison through ordinary continuous module direct image. The declaration's
statement and both original public imports are unchanged.

The private helpers construct the canonical model coefficient map, obtain its
module adjunction from the supplied algebraic inverse image, prove the square
of model and original constant coefficient maps, and transport the adjunction
through the two specified `sfCbcModelModules` equivalences. For an open immersion,
the proved open-map/site-base-change adjunction gives ordinary inverse image.
The explicit identity-on-underlying-schemes comparison with the slice forgetful
functor, together with uniqueness of `sfCbcConstantSliceMap`, identifies its
coefficient map with the prescribed slice map. Module pushforward composition
then gives literal slice restriction. No alternative coordinate equivalences
are substituted for the fixed functors in the statement.

Added one proof dependency module,
`Sheaf.CategoryTheory.ConstantInverseImageScalarNormalization`. It isolates the
ring-only part of the old node's Step 2: equality between the scalar map of a
coherent algebraic inverse-image lift and the transpose of the canonical
constant-section map. It involves no modules, open immersions, slice objects,
AsSmall transport or natural isomorphism of module functors. The rest of the
argument is implemented in the assigned module. Other proof imports reuse the
proved generic supplied module adjunction and the proved open-site helpers.

Updated the assigned DAG node's proof, proof dependencies and proof origin;
added the scalar-normalization node. No existing statement, definition, target,
consumer module or unit route changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.sfCbcOpenRestrictionModelComparison` (node
`lem-sf-constant-open-restriction-model-comparison`). The assigned module has
zero remaining `sorry`s. All its private helpers are proved.

Added one hole:
`CategoryTheory.ConstantCompletion.constantInverseImageScalarNormalization`,
in the new module of the same final component, node
`lem-sf-constant-inverse-image-scalar-normalization`.
Its entire proof is `:= by sorry`; its docstring contains the source and the
complete ring-only argument, including the universal-polynomial uniqueness
argument and the empty-topos case.

This is a decomposition: one original hole closed and one strictly smaller
ring-normalization hole added, net zero. It does not claim a completed proof
independent of the new lemma or of existing library obligations.

## No longer needed

No original import is removed, and no Lean module is withdrawn.

The old direct proof dependencies
`lem-weil-pbc-proetale-ringed-open-comparison` and
`lem-weil-pbc-ringed-topoi-module-adjunction` are not used: the former's
existential coefficient equivalence does not specify the fixed coefficient
transports, while the proved supplied tensor/module adjunction applies to the
fixed lift. Their modules are not newly imported.

The old direct dependency
`lem-weil-proetale-weakly-etale-localization` is replaced in this proof by the
already constructed concrete slice functor and the proved open-site adjunction.
Localization remains behind the existing slice functor and its continuity;
no global withdrawal or pruning of that node is claimed.

The exploratory import `Sheaf.Paper.CompletedPullbackAdjunction` is not retained;
the independently sized supplied adjunction and its precise coefficient tensor
helper suffice. No completion or derived pullback result is used in the new
argument.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly separated the fixed coefficient comparison from
existence of an arbitrary ringed-open equivalence. Its assertion that the
algebraic lift preserves each specified constant section needs an additional
argument: `InverseImageData.constants` is a natural isomorphism of ring-valued
functors, but its structure does not include the displayed unit equation.
The remaining scalar lemma derives that normalization from its existing
naturality and algebraic graph equations, rather than adding it as a hypothesis
or changing the chosen inverse-image data.

The new lemma is strictly a coefficient step. Its application supplies the
scalar equation required by the proved module adjunction; the assigned proof
still constructs and composes all module, model and slice comparisons.
Empty schemes, the zero ring and non-quasi-compact open immersions introduce
no additional hypotheses. The unit route in `sk-thm-sf-identification` stays intact.

## New nodes

`lem-sf-constant-inverse-image-scalar-normalization`, stated in
`lean/Sheaf/CategoryTheory/ConstantInverseImageScalarNormalization.lean`, records
only the ring-normalization calculation from Step 2 of the assigned node.
Its statement is an equality of set-sheaf maps for arbitrary small sites and
constant commutative rings. Its proof plan first constructs the canonical
comparison from terminal objects and coproducts, uses the universal polynomial
and integer evaluations to rule out a natural automorphism of constant rings,
and concludes through the two Hom equivalences. The node records LeanSearch,
LeanFinder, grep and blueprint searches. No change record is needed because no
existing statement or definition changes.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
