## What changed

Constructed `finiteScalarPullbackComparison` as the inverse mate of the specified,
constant-section-normalized derived direct-image comparison. The construction proves
that the two intrinsic direct-image presentations agree by the coefficient adjunction
Hom bijection, derives that equality, and uses invertibility of inverse mates along
equivalences. Its data has no postponed proof or arbitrary existence witness.

Replaced the projection-presentation hole by a categorical proof. The existing
projection/mate identity supplies the commuting arrow square, with tensor and mate
isomorphisms as endpoints. Naturality along the two realization counits then changes
realized inverse-equivalence inputs to the actual inputs K and L. Neither properness
nor projection invertibility is used.

The scalar tensor and inverse-image square is isolated in its own module. It states
tensor bifunctor isomorphisms and their compatibility with the normalized pullback
comparison; it contains no projection map. This is a strictly earlier step of the
source argument, with the adjunction and final arrow assembly proved in the item.
The curried intrinsic tensor-pullback map includes the canonical currying/precomposition
isomorphism; its component is the original uncurried comparison. Original declarations,
signatures, definitions and public imports are preserved.

Validation: `lcompile.py --all` compiled the new comparison module (10.3 s).
A subsequent single-file compile of the final presentation module passed without
warnings (6.1 s). Both files satisfy the 60 s limit; no shared interface is changed,
so there are no forced importer adaptations.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.finiteScalarProperProjection_presentation`
(node `lem-sf-finite-scalar-proper-projection-presentation`).

Added one hole:
`WeilConjectures.finiteScalarTensorPullbackComparison`, in the new module
`Sheaf.Paper.FiniteScalarTensorPullbackComparison`
(node `lem-sf-finite-scalar-tensor-pullback-comparison`).

Thus this is a decomposition: one original hole closed, one simpler tensor-square
hole added, and zero net holes eliminated. The pullback comparison construction and
the two private arrow-isomorphism helpers are fully proved. The delivery has exactly
one explicit `sorry`, the entire proof of the new named public theorem.

## No longer needed

No module or node is withdrawn. No original public import is removed: their symbols
remain in the original declarations. The original generic constant-scalar restriction
and derived projection identification dependencies remain needed for the tensor
step and are recorded on its new node. The parent now uses the already proved
categorical projection/mate square rather than restating that categorical argument
as another obligation. No realized blueprint-unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan does not provide a directly applicable declaration identifying
the specified pro-etale associated-module-sheaf realization and arbitrary supplied
intrinsic tensor models with the published fixed-scalar tensor comparison. The
generic constant-module identification has geometric, exactness and normalization
data as parameters; the ordinary total-tensor realization theorem provides only
objectwise isomorphism existence. Neither signature directly supplies the natural
normalized tensor-pullback square needed here. This missing specialization is now
explicitly stated, with its source and full mathematical proof in its docstring.

Also, the constant-module and ringed direct-image functors use propositionally equal
coefficient maps, not definitionally identical maps. The proved pullback comparison
construction accounts for this equality before taking inverse mates. There is no
statement dispute and no change to the meanings of the target statements.

## New nodes

`lem-sf-finite-scalar-tensor-pullback-comparison`, realized by
`WeilConjectures.finiteScalarTensorPullbackComparison`, isolates the constant-scalar
tensor and inverse-image compatibility step (Stacks 07A4 and the adjunction
normalization of 07A6). The source, dependencies, proof in words, Lean attachment
and four recorded search queries are in its node. The original node's proof,
proof dependencies and proof origin follow the new projection-arrow proof.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
