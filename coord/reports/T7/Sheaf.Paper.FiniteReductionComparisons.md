## What changed

Proved four declarations in the item module: `finiteReductionPullbackPresentation`,
`finiteReductionCoefficientSquare`, `existsUnique_finiteReductionUnitSectionMap`, and
`finiteReductionCompactSupportComparison_isIso`. The compact-support proof uses the
proof-only import `Sheaf.Paper.FiniteCompactSupportConstructibility`, whose canonical
finite-level scalar-mate comparison is definitionally the map in this module. The
section-map proof supplies explicit coefficient-ring types for sectionwise units.
No statement, definition, visibility, or public import was changed.

## Proved and sorry left

Four of the eight source holes are proved:

- `WeilConjectures.PurityFiniteSetting.finiteReductionPullbackPresentation`
- `WeilConjectures.PurityFiniteSetting.finiteReductionCoefficientSquare`
- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionUnitSectionMap`
- `WeilConjectures.PurityFiniteSetting.finiteReductionCompactSupportComparison_isIso`

Four textual holes remain, all from `def-pur-finite-reduction-comparisons`:

- `existsUnique_finiteReductionSourceComparison`
- `finiteReductionUnitComparison_isIso`
- `existsUnique_finiteReductionExceptionalComparison`
- `finiteReductionExceptionalComparison_isIso`

No holes were added and no statements were split off.

## No longer needed

No imports, nodes, or modules were pruned. The proof uses the existing source imports
and the proof-only `Sheaf.Paper.FiniteCompactSupportConstructibility` import.

## Where the brief, the DAG or earlier work was wrong

The earlier section-map attempt omitted explicit coefficient-ring types for the
sectionwise element `1`; restricted module sections expose only an additive structure
until those types are supplied. The exceptional-map node cited in the docstring,
`lem-coef-finite-exceptional`, has no Lean attachment in the current sources and was
not invoked. The remaining four holes require the source-root and exceptional comparison
arguments described in their docstrings.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
