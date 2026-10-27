## What changed

Replaced the remaining proof of `WeilConjectures.SemilinearSections.systemBlockGeometry`.
The proof uses a repeated ordinary inverse-system/direct-core construction, applies the
existing `ordinaryDirectSystem_homData_exists`, proves both naturality equations, and
constructs the system adjunction using `Adjunction.mkOfHomEquiv`. The component square
equations prove compatibility of the ordinary Hom equivalences with repetition.
Applying that identity to an identity map and to the original counit proves the two
required adjunction equations. Additivity follows from exactness and the right-adjoint
criterion. The ringed sequence-site Grothendieck theorem and the existing K-injective
instance supply resolutions on the repeated coefficient category. Private helpers
in the new assembly module carry out the component transposition and adjunction-square calculations with abstract category
parameters, avoiding repeated unfolding of the ringed-site definitions.

Added proof imports of `Sheaf.Paper.BlockGeometricCore`,
`Sheaf.Paper.BlockGeometricAdjunctionAssembly`, the additive adjunction API,
the ringed-site Grothendieck theorem, and the source Grothendieck K-injective instance. Existing public declarations,
statements, definitions and public imports are unchanged. Updated only the proof,
proof dependencies and proof origin of the item's node.

## Proved and sorry left

Closed the item's one original hole, `WeilConjectures.SemilinearSections.systemBlockGeometry`
(node `lem-pur-system-block-repetition`), by reduction to a strictly local construction.
The item module has zero holes remaining. The new theorem
`WeilConjectures.SemilinearSections.blockGeometricAdjunctionAssembly`
(node `lem-pur-block-geometric-adjunction-assembly`) is completely proved, with
zero holes in its module. Added one named hole:
`WeilConjectures.SemilinearSections.blockGeometricCore`
(node `lem-pur-block-geometric-core`), in `Sheaf.Paper.BlockGeometricCore`.
This is a decomposition: one hole closed, one added, net zero. The remaining lemma
constructs the repeated component functors and the local two-component transition mate,
with normalized repetition squares; it asserts neither a global Hom equivalence nor
a system adjunction, its naturality, either unit/counit equation, K-injective existence,
or any derived comparison. These assembly steps are proved in the new assembly
module and applied in the item.

The new statement was checked on identity repetition, indices inside one block,
zero coefficient rings and non-flat transitions. It needs no added finite-limit
hypothesis on `uInv`: the supplied `Geometry` already gives the exact module inverse
images and the normalized coefficient-restriction comparisons used by the construction.

## No longer needed

None. No existing imports, nodes or modules are pruned. The endpoint adjunction,
abstract derived-comparison route, and open-localization route are retained.
The added local construction is needed by the completed ordinary-adjunction assembly.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The generic ordinary-system existence theorems require
`PreservesFiniteLimits uInv`, which is not a hypothesis of this item; the local
construction instead uses the exact module functors and restriction comparisons
already supplied by `G`. No additional hypothesis is imposed. The previous proof plan did not expose the local repeated
ordinary geometric core as a separate Lean declaration. This delivery isolates that
construction and uses the already proved component Hom assembly instead of leaving
the complete global adjunction and both compatibility equations inside the original hole.
Zheng Construction 4.1 and the paragraph immediately preceding Lemma 4.10 were read
in the local PDF (printed pages 21 and 23). The finite-block specialization is the
agent generalization already recorded by the original node. The unit route is retained.

## New nodes

`lem-pur-block-geometric-core`: local construction of the repeated inverse-system and
direct core with prescribed component functors, local transition-mate condition, and
section-normalized repetition squares. Its docstring and node give the complete
construction in words. Mathlib semantic, name and source searches find the general
module-sheaf adjunction API but not this normalized reindexed construction.

`lem-pur-block-geometric-adjunction-assembly`: completely proved assembly of the
repeated ordinary adjunction and both repetition unit/counit equations from
the local cores and normalized evaluation squares. This module contains the
proved private categorical helpers extracted to meet the compilation limit.

No existing shared module interface was changed, so no change record or forced
consumer adaptation is needed.

Validation: final `lcompile.py --all` passed with no warnings: the proved assembly
module took 25.4 seconds, the local construction module 5.1 seconds, and the item
47.3 seconds. The extraction follows improvements to the concrete application
(explicit functor arguments and local irreducibility), so every file meets the
60-second bound. No shared definition or interface was changed. All Lean lines
are at most 100 characters; development-profiler options are absent.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
