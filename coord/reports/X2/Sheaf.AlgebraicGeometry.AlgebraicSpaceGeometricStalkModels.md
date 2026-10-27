## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.SingleComplex.stalkModel_nonempty` and
`AlgebraicGeometry.AlgebraicSpace.SingleComplex.stalk_additive` in the assigned module.
A proved private helper transfers the existing cofilteredness theorem for all pointed
étale charts to the chosen small affine basis: restrict to an affine open through the
geometric lift, then transport through the small-model equivalence. The stalk model
uses the actual ring colimit and Mathlib's varying-ring module colimit functor; the
colimit cocones give its germs and universal properties. The map and scalar equations
are Mathlib's equations on colimit generators. Additivity follows from the colimit
adjunction and the inverse of the sectionwise additive restriction equivalence.

Added private proof imports for the existing pointed-neighbourhood theorem, filtered
category transfer, smallness of structured arrows, varying-ring module colimits,
ring colimits, and additivity of adjoints. Updated the item's node proof and its proof
dependencies. No public signatures, definitions, attributes or public imports changed.
No other existing module was edited.

## Proved and sorry left

Closed 2 of the original 4 holes, with no holes added and no statements split off:

- `AlgebraicGeometry.AlgebraicSpace.SingleComplex.stalkModel_nonempty`.
- `AlgebraicGeometry.AlgebraicSpace.SingleComplex.stalk_additive`.

Two original named holes remain, both attached to
`def-sfb-space-geometric-stalk-models`, with their source and natural-language proofs
unchanged:

- `AlgebraicGeometry.AlgebraicSpace.SingleComplex.stalkMap_existsUnique`.
- `AlgebraicGeometry.AlgebraicSpace.SingleComplex.pullbackStalk_existsUnique`.

The proof uses the existing stated theorem
`AlgebraicGeometry.AlgebraicSpace.pointedEtale_small_cofiltered`; that theorem's
own hole is unchanged in its existing module. This is a partial proof delivery,
not a claim that the stalk comparison theory is now sorry-free.

## No longer needed

None. All existing public imports remain necessary to the existing interface. No
nodes or modules are withdrawn. The original node had no proof dependencies to
prune; the delivery records the existing dependencies its proof actually uses.
No new decomposition lemmas or duplicate stalk constructions were introduced.

## Where the brief, the DAG or earlier work was wrong

The item's definition node originally had an empty proof and proof-dependency list,
although the module contained four proof obligations with proofs in their docstrings.
The delivery records the implemented existence and additivity arguments and explicitly
identifies the two unchanged obligations. Cofilteredness for all pointed algebraic-space
scheme charts was already stated in `SpacePointedEtaleNeighbourhoodsCofiltered`; it
is reused, with an explicit affine-basis refinement, rather than restated. The unit's
route and every existing theorem statement are preserved.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
