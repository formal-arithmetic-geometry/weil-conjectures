## What changed

Repaired the returned delivery by keeping `diagonalTower_limit` as the explicit unresolved
stage-3 theorem, rather than moving its binders and conclusion into a vacuous helper. The
unused endpoint and completed-hom split modules and their imports were removed. The shared
interface extraction remains, and the completed-limit specification is isolated in a
standalone definition module so each file compiles within the limit.

## Proved and sorry left

No theorem hole was closed in this repair. `diagonalTower_limit` remains the single `sorry`.
No definitions contain `sorry`.

## No longer needed

The unused `diagonalTower_ordinaryEndpoints`, `diagonalTower_endpointCompletion`, and
`diagonalCompletedUnderlying_hom_bijective` modules and nodes were removed from this repair
because no written proof uses them. The vacuous `diagonalTower_limit_core` split and its
assembly proof route were removed. The interface extraction is still imported by the item;
its five direct importers are:

- `Sheaf.Paper.CanonicalDiagonalRightDerived`
- `Sheaf.Paper.DiagonalTowerTraceLimit`
- `Sheaf.Paper.DiagonalTowerTraceModels`
- `Sheaf.Paper.DiagonalTraceSources`
- `Sheaf.Paper.RationalP1Triangle`

## Where the brief, the DAG or earlier work was wrong

The returned route moved the item's full binders and conclusion into a helper with a
vacuous hypothesis and did not use the helper lemmas it introduced. This repair removes that
movement and leaves the target hole in place, as permitted by the return instruction. The
assembly node is now a definition node whose Lean statement is the actual
`DiagonalCompletedLimitSpec` signature, and the interface node records the actual
`DiagonalRlim` structure signature.

## New nodes

- `def-sfb-diagonal-limit-interface`
- `def-sfb-diagonal-limit-assembly`

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
