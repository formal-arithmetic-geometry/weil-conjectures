## What changed

Retired the assigned duplicate Sheaf module by listing
`lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedRootSectionEtaleDescent.lean` in
`deleted.txt`. Repointed node `lem-sbc-punctured-root-section-etale-descent` to the already
proved adopted source declaration
`WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent` and updated
its proof metadata to the source theorem's direct finite-presentation descent route.
The required change record is `coord/changes/T2-retire-punctured-root-section-etale-descent.md`.

## Proved and sorry left

This is a retirement repair with zero initial holes. The adopted source theorem is already
fully proved; no `sorry` is added and no `sorry` remains in the retained source module.

## No longer needed

The duplicate Sheaf section-descent module and its old strict-henselization comparison glue
are no longer needed. Its duplicate root-limit and structural-map dependencies are removed
from this module's import closure. The source theorem's upstream root-limit presentation and
finite-presentation factorization dependencies remain in use by the retained source module.

## Where the brief, the DAG or earlier work was wrong

The live module had already been proved, but the retirement assignment supersedes retaining
the duplicate. The source twin has a different canonical strict-henselization interface;
the DAG node is therefore attached to the source theorem's exact declaration while its
natural-language statement and target route are unchanged. The only source consumer already
imports and invokes the source theorem, so no consumer adaptation is required.

## New nodes

None.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
