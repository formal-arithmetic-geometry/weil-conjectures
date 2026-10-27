## What changed

Kept the statement of `WeilConjectures.commonProjectionTensorCompatibility` unchanged.
Constructed its shared tensorator explicitly, independently of the morphism and
compactification, in `Sheaf.Paper.CommonProjectionTensorComparison`.
Its naturality is proved from the existing common-stage tensor representative
formula, in the support modules `CommonStageInclusionTensorModel` and
`CommonStageInclusionTensorNaturality`. The scalar unit removes the reflexive transition on both inputs;
the prescribed tensor normalizations then give the operation-coordinate tensorator.
The invertibility of the coefficient prime on each six-functor space is proved
from the base-field characteristic and the maps to residue fields.

`Sheaf.Paper.ProjectionMateFactors` defines the actual intermediate proper-image
object, the proper counit factor, the open factor, and their coefficient comparison.
Its factorization theorem expands the existing projection formula and cancels only
the two transports at the intermediate object. Its general theorem
`projection_preserved_of_factors` pastes the two factor squares by functoriality
and associativity and recombines these actual factors. The item instantiates
this proved theorem with the two common-stage factor compatibility statements.

The two factor compatibility calculations are separate modules, each with its
source, full proof in words, precise intermediate endpoint, and DAG node.
No existing dependency module, target, definition, or statement is changed.

Validation: `lcompile.py --all` accepted all seven delivered modules, including
the assembled item proof. No profiling option remains in the delivered files.

## Proved and sorry left

The original sole hole, `WeilConjectures.commonProjectionTensorCompatibility`, has
a complete Lean proof from two strictly smaller factor squares. This is a
decomposition, not a completed proof of the whole mathematical obligation:
one upper hole is removed and two lower holes are added.

Proved without new holes:

- `WeilConjectures.commonInclusionTensorModel_naturality`;
- `WeilConjectures.sixFunctorSpace_coefficient_invertible`;
- `WeilConjectures.ProjectionCoefficientTransport.middle_eq`;
- `WeilConjectures.ProjectionCoefficientTransport.projection_factorization`;
- `WeilConjectures.ProjectionCoefficientTransport.projection_preserved_of_factors`.

The tensorator and the factor maps are actual constructions, with no sorry in
any definition. The tensorator uses the existing uniquely specified common-stage
tensor, not a choice of an isomorphism from mere existence.

Every sorry remaining in this delivery:

- `WeilConjectures.commonProjectionProperFactor`, node
  `lem-sf-common-projection-proper-factor`: preservation of the proper counit factor
  and the initial support identification; contains no open projection.
- `WeilConjectures.commonProjectionOpenFactor`, node
  `lem-sf-common-projection-open-factor`: preservation of the proper image of the
  open projection and final support identification; contains no proper counit mate.

These statements do not repackage the full compatibility theorem: their common
middle object is the actual output of the proper factor before the open map.
Neither statement asserts the composite projection square or the existence of a
shared tensorator. Zero inputs, empty schemes, and identity opens/extensions use
the same formulas. No projection invertibility or rational coherence is assumed.

## No longer needed

No existing public or private import was removed, and no existing module is withdrawn.
No mathematical dependency of the original proper/open plan is claimed pruned:
the operation stages, completed pullback/tensor comparison, tensor representative
formula and coefficient categories remain needed below the factor lemmas.
The original node's direct proof dependencies now name the constructed tensorator,
the proved factorization, and the two factor squares, matching the actual Lean proof.
The public import of `RationalProjectionTensorCompatibility` remains necessary for
its endpoint definitions; its unproved compatibility theorem is not used.

The per-square tensorator in `SixFunctorExchangeComparison` is not used to choose
the shared family. It is permitted to depend on the square and is not identified
by its signature with a single canonical tensorator. The component-only
`CommonStageInclusionTensorComparison.stageTensor_existsUnique` is also unnecessary
for this construction: the existing tensor representative specification supplies
both the components and their naturality directly.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The plan is valid but its steps 2--4 require real proper/open
coefficient-square calculations that the existing per-square comparison field does
not itself supply for a common tensorator. The delivery exposes these two missing
calculations rather than assuming all per-square tensorators coincide.

`blueprint_refs.py ancestor lem-sf-common-projection-tensor-compatibility` returns
None because the historical created.item chain stops at a module name. New nodes
record that result, while their source and proof places explicitly name the current
blueprint's Compatibility paragraph and the assigned node's corresponding steps.

The first monolithic version was correct but over 60 seconds. After profiling,
I made the new tensor definitions irreducible, moved cancellation to a general
categorical lemma, and disabled the expensive let-to-have transformation in these
new modules. The combined file was still too slow, so the completed model,
naturality and operation normalization are now separate modules as permitted by
the current brief. No shared definition was changed and no limit was raised.

## New nodes

`def-sf-common-stage-inclusion-tensor-model`: the explicit model isomorphism before
applying the scalar unit; module `Sheaf.Paper.CommonStageInclusionTensorModel`.

`lem-sf-common-stage-inclusion-tensor-model-naturality`: its proved naturality and
the resulting raw natural tensorator; module `Sheaf.Paper.CommonStageInclusionTensorNaturality`.

`def-sf-common-projection-tensor-comparison`: the natural canonical tensor comparison,
and the coefficient-prime invertibility lemma;
module `Sheaf.Paper.CommonProjectionTensorComparison`.

`def-sf-projection-mate-factors`: the intermediate object, exact proper/open factors,
proved factorization, and intermediate coefficient comparison;
module `Sheaf.Paper.ProjectionMateFactors`.

`lem-sf-common-projection-proper-factor`: the proper counit-factor comparison square;
module `Sheaf.Paper.CommonProjectionProperFactor`.

`lem-sf-common-projection-open-factor`: the open-factor comparison square;
module `Sheaf.Paper.CommonProjectionOpenFactor`.

There are no change records because no existing interface is changed.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
