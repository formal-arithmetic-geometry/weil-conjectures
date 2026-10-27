## What changed

Filled the item theorem with a real proof that extracts a pro-etale local trivializing
cover from finite local freeness of rank one and applies the new local descent theorem.
Added `Sheaf.Paper.DiagonalCompletedLineCompleteAux` with the named lower theorem
`diagonalCompletedLine_complete_of_cover`, whose proof remains a documented split-off
`sorry`. Added its DAG node and updated the item's node proof and proof dependencies.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompletedLine_complete`.
The new theorem `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompletedLine_complete_of_cover`
remains as one split-off sorry, with node
`lem-sfb-diagonal-completed-line-complete-aux`.

## No longer needed

The item proof directly needs only the local descent theorem and the locally free
rank-one API. The former proof dependencies
`det-pe-wc-sections-exact`, `lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-flat-ringed-ideal-complete-equivalence`, and
`lem-sfb-source-principal-completion-orthogonal` are no longer direct dependencies of
the item; they remain dependencies of the split-off theorem. No existing module is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior item proof plan exposed the local trivialization/descent argument but had no
Lean interface for that step. The added cover hypothesis makes this step explicit and
strictly reduces the item to a local completeness assertion. No target statement or
definition was changed.

## New nodes

`lem-sfb-diagonal-completed-line-complete-aux` records the local trivialization,
regular completed-module calculation, principal orthogonality, and descent step. Its
Lean declaration is in
`lean/Sheaf/Paper/DiagonalCompletedLineCompleteAux.lean`.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
