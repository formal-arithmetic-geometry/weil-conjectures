## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.smallModuleRestriction_isEquivalence` using the actual small affine étale inclusion and the unchanged identity comparison of structure rings. Private helpers construct the affine open charts of every étale chart, prove that their arrows cover, and factor the covering arrows through the small skeleton. Thus the inclusion is full, faithful and cover-dense; Mathlib supplies dense-subsite comparison for additive sheaves in the original section universe.

Added `Sheaf.CategoryTheory.DenseSubsiteModuleExtension`, with the fully proved general theorem `SheafOfModules.denseRestriction_isEquivalence`. It extends module morphisms by dense comparison. For objects it extends the additive sheaf and scalar action, verifies module axioms through an injective map to a product of restricted modules, and lifts the additive counit to a module isomorphism. The construction uses no new existence obligation. The item imports this theorem, the representable étale scheme tests, and Mathlib's induced-topology dense-subsite API as proof-only imports. All existing public imports, declaration signatures, instances and definition bodies are preserved.

Both delivered modules compiled cleanly together through `lcompile.py --all`: the general comparison module in 14.1 seconds and the item in 6.4 seconds.

Updated the item's node proof and dependencies to record this argument. No other existing module or node is changed, and no change record or forced adaptation is needed.

## Proved and sorry left

Closed one of the item's original two holes:
`AlgebraicGeometry.AlgebraicSpace.smallModuleRestriction_isEquivalence`
(node `def-sfb-space-small-ringed-model`).

The sole remaining hole is the unchanged
`AlgebraicGeometry.AlgebraicSpace.affineEtaleCharts_essentiallySmall`
(node `def-sfb-space-small-ringed-model`). The proved equivalence uses this existing instance to form the small skeleton; it does not claim to establish its size bound.

Added zero holes and split off zero unproved statements. The new general theorem and all its private helpers are proved. The existing proof of `smallStructurePresheaf_isSheaf` is preserved.

## No longer needed

None. No existing imports, modules or nodes are pruned. The original node had no stated proof dependencies to discard. The unit's route and all its realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original node did not provide proof steps for this module. The added steps explain the affine-cover argument and the action extension needed beyond Mathlib's additive-sheaf comparison. Search found dense comparison for sheaves, but no general dense-subsite comparison theorem for `SheafOfModules`.

The general module theorem has no nonempty-site, affine, commutative-ring or finiteness assumption. If an image covering sieve is empty, sheaf separatedness still proves the injectivity used in transferring module axioms. On the identity subsite the extended action agrees with the given one. These edge cases require no additional hypotheses or change of section universe.

## New nodes

`lem-sfb-dense-subsite-module-extension` records the fully proved general module comparison theorem in `lean/Sheaf/CategoryTheory/DenseSubsiteModuleExtension.lean`. Its hypothesis is equivalence of additive-sheaf restriction on a dense subsite, and its conclusion is equivalence of the actual module restriction functor with identity ring comparison. Its four proof steps are full faithfulness, extension of the scalar action, transfer of module axioms through an injective additive map, and the linear counit isomorphism. Sources and Mathlib searches are recorded in the node. No new unproved intermediate statement is introduced.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
