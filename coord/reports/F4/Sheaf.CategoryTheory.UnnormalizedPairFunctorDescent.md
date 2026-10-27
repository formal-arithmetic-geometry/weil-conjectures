## What changed

Proved `CategoryTheory.StageSystem.unnormalizedPairFunctorDescent` in
`Sheaf.CategoryTheory.UnnormalizedPairFunctorDescent`, preserving its entire statement,
universes and hypotheses. Reused the proved source-library `StageSystem.Morphism` API
for every existing descent law. Constructed both whiskered compatible families directly:
post-whiskering uses naturality of the outer comparison followed by `Hom.comm`, and
pre-whiskering uses `Hom.comm` followed by naturality of the stage transformation.
Componentwise equality descends by natural-transformation extensionality.

The node now records reuse of `Morphism.tr_mapAt` rather than repeating its proof, and
identifies the Lean calculations for whiskering and equality. The unit has no realized
proof steps, and its route is preserved. No source-library file changed. The original `[Nonempty I]` hypothesis is retained;
`linter.unusedSectionVars` is disabled locally for this theorem because the stronger
source API needs no nonempty-index hypothesis.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.StageSystem.unnormalizedPairFunctorDescent`
(node `lem-pur-unnormalized-pair-functor-descent`).

Holes closed: 1. Holes added: 0. Sorries left in delivered Lean modules: 0.
No split-off statements or new declarations. Remote lcompile checked the complete
proof in 2.0 seconds; its only warning was the retained unused section hypothesis,
addressed by the local linter option. Delivery validation checks the final file.

## No longer needed

The independent transport calculation in the old plan is unnecessary because
`Morphism.tr_mapAt` is already proved and recorded in
`lem-pur-associative-stage-family-descent`. Both original DAG dependencies remain
needed: the unnormalized pair construction and the source Morphism declaration family.
No mathematical node is withdrawn.

Removed `public import Sheaf.CategoryTheory.ExactStagePairData`: the statement uses
only the general `StageSystem` interface, already publicly supplied by
`WeilConjectures.CategoryTheory.StageSystem.Functor`. No exact, shift or triangle data
are used. There are no current direct Lean importers of the item (checked by rg and
an exact import-line scan); its planned DAG parent has no Lean attachment yet.
The definition node `def-sf-directed-common-stage-data` remains a statement dependency
for the general pair notion. This does not withdraw its module or affect other users.
Change record: `coord/changes/F4-unnormalized-descent-import.md`.

## Where the brief, the DAG or earlier work was wrong

The DAG proposed a separate transport proof although its cited existing declaration
family already includes the exact transport theorem. The short source API route
preserves every clause, including repeated indices and independent universes. The
whiskering constructions use no unitor, exactness, faithfulness or normalization.

Searches run through msearch.py: leanfinder for coherent directed-stage descent,
loogle for `CategoryTheory.Functor.whiskerRight`, and grep for
`descNatTrans|functor_comp_map|tr_mapAt`. Mathlib supplied generic whiskering only;
reading the source `StageSystem/Functor.lean` found all other needed laws.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
