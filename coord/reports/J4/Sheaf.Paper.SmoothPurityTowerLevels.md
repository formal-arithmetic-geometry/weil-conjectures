## What changed

Proved all three original theorem holes in `Sheaf.Paper.SmoothPurityTowerLevels`.
The tower pushforward has a left adjoint by the Grothendieck adjoint functor theorem.
Its exactness and evaluation comparisons follow from two separately proved ingredients:
finite-level inverse-image exactness and commutation of right extension with tower
pushforward. The latter uses the adjunction unit, whose level-n component is invertible;
compatibility with bijective upper transitions proves invertibility above n, while
zero objects handle the lower levels. The derived comparison uses the existing
natural derived tower evaluation theorem and exact-functor comparison isomorphisms.
All three delivered modules compile without warnings against the current library.
The latest dry run compiled all modules but its automatic axiom probes timed out;
the delivery tool schedules those probes to run again at merge. This packet does
not claim a completed axiom audit of its dependency closure.

## Proved and sorry left

Closed the three original holes: `sp_tower_operations_exist`,
`sp_tower_operations_properties`, and `sp_tower_levels`.
Also proved the new supporting theorems `sp_level_pullback_exact` and
`sp_tower_push_right_extension`. Holes added: zero. Holes remaining in the
three delivered modules: zero. No unfinished split theorem remains.

## No longer needed

Removed these redundant proof imports from the item module:

- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.SmoothPurityCoefficientTowers`
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`
- `Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint`

Removed the unused `Mathlib.CategoryTheory.Adjunction.Whiskering` proof import
from `SmoothPurityTowerPushRightExtension`.
Removed `Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint` from
`SmoothPurityLevelPullbackExact`: finite-level exactness uses no tower right adjoint.
These removals are direct-import pruning; the results needed by other library
proofs remain available through their existing dependencies. The old direct tool-use entries for `lem-pur-ringed-site-grothendieck-abelian`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-complex-injective-resolution-mono`, and
`src-right-derived-functor-plus-acyclic-unit` were removed from this node; their
necessary work is provided inside the cited existing ingredient declarations.
No entire unit or library module is claimed globally unnecessary. The existing natural theorem
`sp_tower_derived_direct_image_evaluation` already carries out the unit's injective
resolution argument, so this module needs no second implementation of its
acyclic-resolution and K-injective comparison steps.

## Where the brief, the DAG or earlier work was wrong

The preserved node records described finite-level exactness with the unrelated
right-extension proof. They now describe the actual small-site transport argument.
The earlier packet left the right-extension comparison unfinished; it is now fully
proved. The original node said to avoid the derived comparison already present in
`det-sp-tower-injective-components`; its existing theorem supplies exactly the
natural comparison needed here and already implements the unit's resolution route.
No statement, definition, universe, or target signature was changed.

The first resumed delivery stopped on unused section-instance warnings. After
removing those binders from the helper that does not need them, all modules compile
without warnings. Profiling a later intermittent timeout identified expensive
instance search in the final finite-level theorem lint pass; restoring normal transparency
for that theorem reduced its checked compile to 26 seconds. An earlier delivery check crashed during worktree checkout after
600 seconds; no push occurred in that attempt.

## New nodes

`lem-sp-level-pullback-exact`: proved exactness of the finite-level inverse image,
transporting to the compatible coefficient-sized small pro-etale models and using
the canonical constant-coefficient identification.

`lem-sp-tower-push-right-extension`: proved the ordinary right-extension/pushforward
comparison. The adjunction unit provides the map, the level-n triangle gives an
isomorphism there, upper transition bijections propagate it, and lower zero levels
complete the proof. Both new nodes have fully proved Lean declarations.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
