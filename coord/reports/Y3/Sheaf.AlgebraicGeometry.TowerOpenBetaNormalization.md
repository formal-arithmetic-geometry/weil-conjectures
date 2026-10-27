## What changed

Filled twelve original theorem proofs in
`Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization`. Public declarations,
constructions and signatures are preserved. The proofs establish invertibility,
open-unit normalization, exact descent, evaluation, both module pasting laws,
identity laws, the complex component formula, and invertibility of the finite
presentation comparisons. Private helpers prove the required mate and compositor
identities. The tower node records the completed arguments and retains the planned
steps for the two unfinished clauses.

The calculus import was independently removed by the landed record
`coord/changes/A2-tower-open-beta-import-cycle.md`. The proof uses private elementary
mate helpers and `StrictTowerDirectImageCoherence` without reintroducing that cycle.
No other module is adapted. No definition or target statement is changed.

## Proved and sorry left

Closed 12 of the 14 original holes, all in namespace
`AlgebraicGeometry.ProEtale.StrictTower`:

- `openBetaModule_isIso`
- `openBetaModule_normalized`
- `openBetaNormalization`
- `openBetaEvaluation`
- `openBetaModuleBaseChangeComp`
- `openBetaModuleOpenComp`
- `openBetaModuleBaseChangeId`
- `openBetaModuleOpenId`
- `openBetaOpenId`
- `openBetaComplex_component`
- `openBetaFinitePullHom_isIso`
- `openBetaFiniteOpenHom_isIso`

Two original public holes remain: `openBetaRestriction_normalized` and
`openBetaFiniteCompatibility`, both attached to
`lem-cbc-tower-open-beta-normalization`. Their original statements and source-backed
proof docstrings remain. No holes were added, and no statements were split off.
The complete module compiled through lcompile in 49.3 seconds with profiling;
the final compile without profiling passed in 49.0 seconds (see `compile-final.log`).

## No longer needed

Removed unused private proof imports
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`, and
`Sheaf.SixFunctors.OpenTensorNormalization` from the completed proofs. Their nodes
remain in the DAG's pending section/finite proof plans: this partial delivery does
not claim those nodes are globally unnecessary. No module is withdrawn and no
upstream declaration is removed. The independent A2 cycle repair is not counted
as pruning by this delivery.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. Invertibility of the sheaf mate follows from
full faithfulness of open extension and the essential-image counit formula; it
does not require first proving the section-evaluation clause. The completed
pasting proofs operate directly on the canonical compositor squares, then take
mates. Exact descent compares natural transformations before evaluation.

The attempted direct section proof was not completed. Its geometric pullback
square is straightforward, but composing the section equalities caused expensive
unfolding of nested module direct images. The finite equality attempt depended on
that unfinished calculation and is not included. The original two public holes
are retained honestly; no private unfinished proof or new premise is delivered.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
