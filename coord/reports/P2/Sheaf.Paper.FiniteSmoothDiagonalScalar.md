## What changed

Filled `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothDiagonalScalar` in
`Sheaf.Paper.FiniteSmoothDiagonalScalar`. Its statement, docstring, public imports,
definitions, and existing options are unchanged. Added only private proof imports
and four proved private helpers: `exceptional_scalar_square`, `mate_naturality`,
`dualizing_scalar_square`, and `scalar_section_factor`.

The proof adapts the existing compact-support coefficient exchange calculation to
an arbitrary Cartesian presentation, including the flipped self-product. It
normalizes at the coefficient unit using the proved scalar/pullback unit law,
then applies scalar section-compositor coherence and naturality. The source
library supplies boundedness and finite Tor amplitude of the smooth dualizing
complex; the existing scalar tensor calculation supplies the scalar bound.
No coefficient-flatness hypothesis or orientation is introduced.

LeanFinder found ordinary module base-change results, and Loogle supplied the
generic naturality law; neither supplies this six-functor identity. Source search
found the arbitrary-square calculation in `finite_adjoint_mate_baseChange` and
the generic private calculations in `ExceptionalCoefficientComparison`, which
are reused here without its unrelated field and quotient-coefficient parameters.

Updated the item's DAG proof, proof dependencies, and proof origin to record this
route. No shared module, declaration signature, instance, or definition changes.

The proof passed single-file server compilation in 17.3 seconds. The compiler's
unused-hypothesis warning for `hB` was addressed by explicitly referencing that
unchanged hypothesis. Final clean compilation and axiom preflight are run by
`deliver3.py`. The updated DAG dependency graph has no path from any added proof
dependency back to the item.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothDiagonalScalar`
(node `lem-sp-finite-smooth-diagonal-scalar`).

Added 0 holes. There are no `sorry` declarations in the delivered module and no
split-off modules. The four private helpers are completely proved. The theorem
uses the existing library's hypotheses and proof dependencies; this does not
assert that its entire transitive library dependency closure is sorry-free.

## No longer needed

The proof does not use node `lem-pur-section-scalar-base-change` or its module
`Sheaf.SecSmoothPurity.SectionScalarBaseChange`; removed that planned proof edge
from the item's node. No Lean import of it was present in the original item.
Its first clause uses the standard chosen Cartesian presentation, whereas the
item uses the flipped self-product. Reusing the existing compact scalar exchange
calculation directly handles the required Cartesian presentation and avoids
relying on this still-open higher section theorem. This is pruning of the item's
proof dependency only: the module remains for its other consumers.

Kept `lem-pur-scalar-section-compositor`, which is the second planned step.
No existing public import or library module is removed.

## Where the brief, the DAG or earlier work was wrong

The planned first dependency states the exceptional square on the standard
chosen pullback (with second projection structural). The item instead uses the
flipped square (first projection structural). Applying its first clause verbatim
would therefore leave a Cartesian-presentation transport step. The proof supplies
the arbitrary-square mate calculation directly from existing lower declarations.
The mathematical statement and the unit route remain unchanged. Empty schemes,
relative dimension zero, zero coefficient rings, and non-flat coefficient maps
require no separate choices or nonemptiness assumptions in this calculation.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
