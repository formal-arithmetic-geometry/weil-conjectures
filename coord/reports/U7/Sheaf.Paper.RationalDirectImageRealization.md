## What changed

Proved `AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.modulePush_additive`.
The actual module pushforward preserves addition definitionally, because its maps are
sectionwise maps followed by restriction of scalars. The proof constructs the additive
functor certificate directly. No public signatures, definitions, or imports changed.

## Proved and sorry left

Closed one of the item's two original holes:
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.modulePush_additive`.

One hole remains, unchanged:
`AlgebraicGeometry.Scheme.ContinuousRational.DirectImage.rational_direct_image_realization`
(node `lem-a1-rational-direct-image-realization`). No holes were added or split off.
This is a partial delivery, not a proof of the realization theorem.

The main remaining work is connecting the actual cochain pullback counit and right-derived
pushforward unit to the normalized derived adjunction, then proving the localization
projection and the package coherence equations. Exploratory private adjunction helpers were
removed because the delivered proof does not use them. No existential statement duplicating
the remaining theorem is retained.

## No longer needed

None. No dependency is pruned from the still-unproved main realization theorem.
All original imports and its existing DAG proof plan remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy established. The additivity assertion needs no imported theorem:
it follows from the definition of sectionwise pushforward. The existing larger proof plan
still applies to the remaining realization theorem.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
