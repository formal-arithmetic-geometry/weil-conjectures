## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.alpha_eq_localized_singleAlpha` by comparing
its four ordinary and derived factors on cochain representatives. Private helpers establish
compatibility of exact adjunction units, their Hom equivalences, and the unit-preserving
open compositor. Existing `openBetaNormalization` and
`clopenDerived_section_projector` supply the beta and projector equations; naturality
pastes the equations. No coefficient finiteness or evaluation faithfulness is assumed.

All four public declaration signatures are unchanged. The bodies of `singleJCongr` and
`singleAlpha` are unchanged. The `towerAlpha` construction uses the new generic
`Functor.termwiseCompositeTransformation` wrapper with exactly the original components.
This keeps concrete module functors folded. Private named compatibility predicates also
keep representative equations folded, reducing repeated kernel comparisons. The complete
proof compiled in 44.6 seconds; the diagnostic profiler option was then removed.

The new generic construction is in
`Sheaf.CategoryTheory.TermwiseCompositeTransformation`, publicly imported because the
`towerAlpha` definition uses it. The private `import all` of
`StrictTowerProperOpenArrows` reuses its proved exact-adjunction unit API. No other
module is adapted. The owning node now records the actual proof and dependencies.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.StrictTower.alpha_eq_localized_singleAlpha`, node
`def-cbc-strict-tower-ordinary-proper-open-arrows`.

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0. Split off: 0.
The new generic construction and every private helper have complete bodies and no
`sorry`. Existing imported unfinished theorems remain their own items.

## No longer needed

None. All three original public imports remain necessary for the public constructions
and the proof. No module, node, or declaration is withdrawn. The proof needs no new
unfinished statement. Exploratory changes to `moduleJ` and `jComp` were discarded;
`StrictTowerOpenExtension` is not part of this packet.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had no numbered proof plan. Its existing docstring gave the
localization route, which is now made explicit in the node. No mathematical statement
correction was needed. The concrete termwise construction required a performance repair;
its components and all public signatures are preserved. The sole direct use of
`towerAlpha` is in this item, confirmed with `tools/downstream.py --uses towerAlpha`.

## New nodes

`def-cbc-termwise-composite-transformation` records the generic termwise lifting in
`Sheaf.CategoryTheory.TermwiseCompositeTransformation`. It packages Mathlib's existing
postcomposition functor and composition isomorphisms, and contains no proof hole.
The construction change and complete direct-user table are in
`coord/changes/S9-towerAlpha-termwise-construction.md`.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
