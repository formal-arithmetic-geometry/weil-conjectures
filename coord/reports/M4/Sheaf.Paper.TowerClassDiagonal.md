## What changed

In `lean/Sheaf/Paper/TowerClassDiagonal.lean`, proved
`AlgebraicGeometry.ProEtale.SpTowerClasses.diagonalLine_invertible` by applying
`Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` to
`AlgebraicGeometry.ProEtale.diagonalImmersion_cartier S`. Both declarations are
already available through the existing public import. This follows the existing
docstring's Cartier-ideal/dual argument and keeps all signatures, definitions,
docstrings, imports and the unit route unchanged. No dependency module was edited.

The changed module compiled on the server with exit code 0 (32.3 seconds).
The proof covers arbitrary schemes, including the empty base, because
`diagonalImmersion_cartier` has no extra hypotheses.

## Proved and sorry left

Closed 1 of the item's 2 holes:
`AlgebraicGeometry.ProEtale.SpTowerClasses.diagonalLine_invertible`
(node `def-sp-tower-class-diagonal`). Added 0 holes; split off 0 statements.

The one remaining hole is the unchanged named public theorem
`AlgebraicGeometry.ProEtale.SpTowerClasses.lineEvaluation_existsUnique`
(node `def-sp-tower-class-diagonal`). Its existing docstring describes the
section-normalized scalar-extension comparison and uniqueness argument. It was
not relocated or used to prove the closed invertibility theorem. Constructing
that comparison requires the evaluation/change-of-rings interchange and lifting
the given abelian roots comparison to the finite coefficient modules; this
partial delivery makes no claim to have completed those steps.

## No longer needed

None. No imports were added or removed, no module was withdrawn, and no DAG
node or unit step is bypassed. In particular the diagonal-system and divisor-line
bundle dependencies supply the two declarations used in the proof. The remaining
finite comparison still needs its recorded Chern and coefficient dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The invertibility hole does not need a new
four-chart computation: the already proved `diagonalImmersion_cartier` provides
the Cartier ideal for this exact diagonal, and the source-library divisor-line
bundle theorem immediately proves the requested dual invertible.

Searches performed: LeanFinder for the dual of an invertible sheaf (returned
module-dual and Picard results), Loogle `IsInvertible, _` (unknown identifier,
no usable match), the prescribed grep search (no matches), and direct `rg`
searches in both library roots. Direct source inspection located the exact
Cartier and divisor-line declarations used above.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
