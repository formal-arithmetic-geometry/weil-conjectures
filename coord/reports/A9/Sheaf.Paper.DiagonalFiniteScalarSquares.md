## What changed

Proved `diagonalFinite_scalarSquares` without changing its statement. The integral
comparison uses the existing finite point-basis mate criterion, transporting the
bottom-field integral basis along the actual condensed Z_l identification. The
rational comparison uses `localizedDirectImageComparison_isIso` on the shifted
single complex, whose lower bound is -2.

Proved private helpers convert the canonical restriction square's unit equation
from homotopy complexes to cochain complexes, transport the square to any supplied
`DiagonalRightDerived` model using the universal full unit, and compute its scalar
mate under this transport. Thus invertibility concerns exactly the normalized mate
in the statement. All new imports are private proof imports. Updated the item's
DAG proof and dependencies to the argument used. Validation uses the delivery
script's compilation, hole probes and preflight checks; the public theorem's
statement was also compared textually with the original.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalFinite_scalarSquares`
(node `lem-diagonal-finite-scalar-squares`). No holes added or split off; zero
`sorry` declarations remain in the delivered module. The imported finite-basis and
localization results retain their existing transitive dependencies.

## No longer needed

No existing imports were removed and no modules were withdrawn.
The proof does not need the whole `sk-prop-sfb-qlbar-colimit-x` assertion or a fresh
construction of its integral limits and algebraic-closure colimit: only the existing
`det-prop-sfb-qlbar-colimit-x-invert-ell` exactness clause and the proved localized
direct-image comparison are used for rationalization. Likewise, only the finite-free
detail `det-prop-sfb-cartesian-coefficients-finite-free` is used from the broad
`sk-prop-sfb-cartesian-coefficients` dependency. The item's proof dependencies now
name these actual inputs. The continuity and homology argument is reused through
`Sheaf.Paper.LocalizedDirectImageComparison`, not rebuilt or split off again.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The original plan's finite-free comparison
already has a generic proved mate criterion in the source library; the base
coefficient identification supplies the difference between Z_l and the bottom
intermediate field's integer ring. The full-unit normalization and arbitrary-model
transport still require explicit proofs; an arbitrary isomorphism between the
underlying functors would not suffice.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
