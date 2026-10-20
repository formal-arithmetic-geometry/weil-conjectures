## What changed

Retired the duplicate `Sheaf.RingTheory.IntegralExtensionDimension` module listed as
`retire` in `coord/queue.tsv`. The source library already proves exactly the same
statement as `RingHom.IsIntegral.ringKrullDim_le_and_isMaximal_comap` in
`WeilConjectures.RingTheory.IntegralExtensionDimension`.

Changed the proof-only import and theorem application in the remaining direct
consumer `Sheaf.RingTheory.HopfAlgebra.AugmentationHeight`. The consumer's public
signature, public imports and proof argument are unchanged. Updated the existing
node `lem-weil-pbc-integral-extension-dimension` to attach to the source declaration.
The source statement and its complete proof are textually identical after the
theorem rename. No source-library file is changed. Change record:
`coord/changes/retire-integral-extension-dimension.md`.

## Proved and sorry left

The assigned module had zero holes before this retirement. Holes closed: none (0).
Holes added: none (0). Holes left: none (0). Split off: none (0).
`RingHom.integralExtensionDimension` is withdrawn as a duplicate of the already
proved `RingHom.IsIntegral.ringKrullDim_le_and_isMaximal_comap`. The adapted
`HopfAlgebra.height_ker_counit_eq_ringKrullDim` compiles without holes or warnings.

## No longer needed

Withdrawn module: `Sheaf.RingTheory.IntegralExtensionDimension`.
Removed proof import: `Sheaf.RingTheory.IntegralExtensionDimension` from
`Sheaf.RingTheory.HopfAlgebra.AugmentationHeight`; replaced by the corresponding
source-library import. The node and its mathematical proof dependencies stay:
the same integral-extension theorem is used under its source-library name.
No additional nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open proof, but the current queue assigns a
retirement and the module has been fully proved since 2026-10-12. The retirement
inventory treated the upstream rename as a missing theorem. Reading the source
signature shows that both declarations have identical hypotheses and conclusion,
including arbitrary universes, noninjective maps and the maximal-ideal clause.
`WeilConjectures.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing` already imports
and uses the source version, so it requires no change. The only remaining direct
importer of the Sheaf module is the adapted augmentation-height module;
`tools/downstream.py --uses RingHom.integralExtensionDimension` confirms it is
also the only transitive consumer.

Searches through `msearch.py`: Lean Finder found the maximal-contraction lemmas;
Loogle did not index the project-specific source theorem; grep and direct source
inspection found the exact source-library match. The Stacks source at Algebra
00OJ was checked: the existing source proof follows the same strict contraction
of chains and maximal-contraction argument. The unit route is preserved.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
