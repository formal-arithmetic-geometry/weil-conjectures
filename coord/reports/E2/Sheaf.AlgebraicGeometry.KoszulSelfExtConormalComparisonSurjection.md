## What changed

Restored `lean/Sheaf/AlgebraicGeometry/KoszulSelfExtConormalComparisonSurjection.lean`
from its quarantine copy. The proof was already complete, including the local stalk
surjectivity argument and the global sheaf gluing construction. Its proof-only import
of the withdrawn `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing` was changed to
the adopted source module
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`, which provides the
same `SheafOfModules.existsUnique_hom_of_cover` declaration and compiles in the current
library.

## Proved and sorry left

The module has no `sorry` declarations before or after this repair (0 of 0 current
sorries). The declaration
`AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_comparison_surjection`
therefore remains fully proved, with no new holes.

## No longer needed

Removed the proof import of the withdrawn
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`, replacing it with its adopted
upstream realization. No mathematical dependencies, declarations, or DAG nodes were
pruned. The existing proof dependency `lem-pur-sheaf-hom-cover-gluing` is realized by
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.

## Where the brief, the DAG or earlier work was wrong

The quarantined module's proof imported the retired Sheaf twin of the gluing module.
That twin is an empty withdrawn module in the current tree, so the theorem name was
unknown. The DAG already records the upstream twin as the realization of
`lem-pur-sheaf-hom-cover-gluing`; changing the private proof import to that module is
the required rework repair and does not alter any public signature.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
