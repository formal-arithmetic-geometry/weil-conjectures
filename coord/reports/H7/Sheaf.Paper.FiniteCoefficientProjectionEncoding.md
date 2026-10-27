## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientProjectionEncoding`
by a complete categorical assembly from a tensor-compatible pullback square.
The proved structure method
`CategoryTheory.Adjunction.TensorPullbackCompatibility.projection_isIso_iff_of_equivalences`
uses the existing, proved source-library projection-mate comparison. The two encoding
functors are equivalences, so the mate of the pullback square is invertible everywhere.
One implication transports the projection isomorphism; the other cancels the invertible
endpoint comparisons and reflects invertibility through the encoding equivalence.
All existing public declarations and signatures are preserved. Both predicate
bodies now use constructed native ProjectionContext bundles; their unchanged iff lemmas
are proved by unfolding and rfl, so both canonical arrows are exactly the same.

Added a real structure `CategoryTheory.Adjunction.TensorPullbackCompatibility` containing
the pullback and tensor isomorphisms with their compatibility proof. Its tensor bifunctors
are inferred from the native comparison types, avoiding costly conversions between
equivalent elaborations of derived tensor instances. No object is chosen in a definition.

Added `Sheaf.Paper.FiniteCoefficientTensorPullbackEncoding` for the geometric part
of old proof steps 1--2. Its single postponed theorem concerns only left derived pullbacks and
native tensor bifunctors, with their compatibility equation. It has no projection
morphism, no assertion about invertibility of a direct-image projection, and no
assumption equivalent to the item. Thus this is a decomposition, with a genuine
proved mate-and-cancellation argument in the item, not a renamed obligation.

Updated the item's proof route and added the new theorem's node. No source-library
module is edited. The contexts retain the native category, tensor and adjunction
structures behind irreducible definitions with their existing canonical-map iff API.

## Proved and sorry left

Closed the item's one hole, by declaration name:
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientProjectionEncoding`
(blueprint: `lem-sfb-finite-coefficient-projection-encoding`).
The generic equivalence/mate structure method is completely proved.
The structure has no holes; only its existence theorem is postponed.

Added one hole, the whole public theorem proof:
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientTensorPullbackEncoding`
(blueprint: `lem-sfb-finite-coefficient-tensor-pullback-encoding`).
This is the tensor-compatible pullback comparison from old steps 1--2, with a full
proof in words and edge cases in its docstring and node.

Actual hole counts: item 1 -> 0; new module 0 -> 1. Net closure reduction is zero:
this delivery is a decomposition, not a complete proof of the geometric comparison.

## No longer needed

No existing public import is removed and no module is withdrawn. The item's original
four proof dependencies are no longer needed directly in its categorical assembly.
Three remain needed through the new geometric comparison:
`lem-sf-finite-discrete-encoding-tensor-tor`,
`lem-sfb-internal-module-operations-transport`, and
`lem-sfb-constant-scalar-geometric-adjunctions`.
Their modules are not claimed pruned.

`lem-kun-derived-adjoint-square-comparison`
(`Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`) is unnecessary for
this route. The assembly uses the mate of the left-pullback comparison and proves its
invertibility from the encoding equivalences, rather than first identifying a
separately normalized right-derived direct-image comparison. The new geometric
comparison derives exact left pullbacks termwise and needs no such right-derived
adjoint-square theorem. This removes a planned dependency, not a library declaration.

The existing `lem-sp-categorical-projection-mate-square` is reused; no duplicate
categorical comparison module or node is introduced. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old final step concealed the substantive mate, cancellation and reflection
argument. It is now explicit Lean using the existing source-library theorem.
The old plan's separate right-derived adjoint-square normalization is stronger than
needed for the invertibility equivalence. Its tensor-compatible left-pullback
comparison remains a real geometric obligation; no geometric finiteness or
properness assumption has been added to solve it.

The intermediate statement was checked on identity morphisms, empty schemes, the
zero coefficient ring, zero input complexes, and nonproper scheme morphisms.
The first compile exposed an ambiguous cancellation argument and expensive unfolding
of derived constructions. The cancellation suffix and tensor bifunctor arguments are now explicit;
the complete two-module packet compiles; preflight reached its static metadata checks.
It asserts a change of presentation of pullback and tensor, not a projection formula.

## New nodes

`lem-sfb-finite-coefficient-tensor-pullback-encoding` in
`dag/nodes/sec-six-functors-basics/`: existence of the encoding's native tensor
comparisons and its tensor-compatible left-pullback square, old steps 1--2.
The node records the three kinds of search, the complete geometric proof, its
existing dependencies and the verbatim Lean signature.

Change record: `coord/changes/h7-projection-predicate-elaboration.md` records both
predicate definition bodies and the necessary public import. ProjectionContext bundles
the native adjunction, tensors and comparison once. Both old canonical-map iff statements
remain verbatim and their proofs unfold the native context and close by rfl. No data is
chosen from the postponed existence theorem. Contexts and their fields are constructed.
The direct consumer `Sheaf.Paper.FiniteProperBaseChange`, theorem
`projection_of_encoded_origins`, still applies the unchanged iff in direction
`.2` at exactly its original inputs; it requires no adaptation. An unchanged copy of the entire consumer compiled against
the new packet in 35.2 seconds, then was removed from the sandbox. No target statement
is changed; the two predicate bodies are definitionally normalized with unchanged meaning.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
