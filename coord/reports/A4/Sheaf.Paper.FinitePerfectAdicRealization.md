## What changed

Added an explicit public import of `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`,
which supplies the restriction operation used by the theorem statement. The theorem body remains
an existing named proof hole because the available declarations do not provide the global
finite-level effectivity argument.

## Proved and sorry left

No theorem holes were closed. The existing hole
`AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization` remains, with its source and
proof plan recorded in node `lem-weil-pbc-finite-perfect-adic-realization`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The item source did not compile against the cached dependency snapshot: the declarations
`FinitePerfectModelsCompatible`, `HasUniformFinitePerfectModels`, and
`ringedSiteDerivedRestrictionOfUniverses` were unavailable unless their defining modules were
compiled in the same sandbox. The explicit restriction-universe import repairs the latter
interface dependency. The theorem itself requires the multi-stage effectivity and Roos-limit
argument described in the node; no imported theorem states that conclusion.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
