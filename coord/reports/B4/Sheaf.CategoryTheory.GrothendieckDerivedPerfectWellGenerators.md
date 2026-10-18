## What changed

Replaced the prior explicit free-complex kernel proof by a shorter proof using
`grothendieckDerived_compact_localization_model`,
`derived_exists_perfectSmallClass_core`,
`derived_perfectSmallClass_properties`, and
`compactGenerators_localization_generate`. The image of the compact generating
family lies in the canonical alpha-compact class; its alpha-compact API supplies
smallness and coproduct factorization, while localization generation supplies the
final well-generation clause. Removed all proof imports and sandbox modules that
were specific to the unused free-complex route.

## Proved and sorry left

Closed the original hole `CategoryTheory.derived_exists_perfect_well_generators`.
The item theorem is fully proved and no definition contains `sorry`.

The supporting theorem `CategoryTheory.exists_small_factorization_class_of_compact_localization` remains as a single split-off `sorry`, recorded by node `new-sfb-derived-perfect-well-generators-support-b4`; it is strictly below the item and is the only hole added by this delivery.


## No longer needed

The following prior route modules and nodes are no longer used by this proof:
`GabrielPopescuAbelianCore`, `GrothendieckDerivedExactLocalization`,
`GabrielPopescuDerivedKernelSetGenerators`, `SetGeneratedLocalizationPerfectGenerators`,
`DerivedModuleCompactGeneration`, `GabrielPopescuSmallFreeKernelDetection`,
`SmallFreeComplexModels`, `SmallKernelDetectorsGenerate`,
`CompactGeneratorsAlphaCompactClasses`, and the corresponding B4 split nodes.
The bounded free-complex detection and kernel-generation route is entirely pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan unnecessarily rebuilt kernel generators and quotient
factorization. The existing compact localization model and ambient perfect
small-class theorem already provide the needed source generators, alpha bound,
smallness, and factorization; only the exact-left-adjoint telescope theorem is
needed to descend generation to the target. No statement or unit route is changed. The proof-only linter setting is recorded in `coord/changes/derived-perfect-well-generators-proof.md`.

## New nodes

`new-sfb-derived-perfect-well-generators-support-b4` records the supporting
small-class construction. Its theorem is intentionally limited to essential
smallness, shift closure, alpha-smallness, coproduct factorization, and inclusion
of localization images; the importing target proves the generation conclusion
from the compact-generator telescope.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
