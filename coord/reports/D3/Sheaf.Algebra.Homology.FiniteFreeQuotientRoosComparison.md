## What changed

Restored the complete H8 proof of
`CategoryTheory.PrincipalQuotientCompletion.finiteFreeQuotientRoosComparison`
from repair record ef5b5e60103800ab and repaired its accidental instance-environment
change. Removed the proof import of `Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion`.
Proved the required regular-tensor unitor and single-tensor quotient component
identities privately instead, using their existing sheafification and single-tensor APIs.
Kept all reducibility hints local and scoped the theorem statement transparency separately from its proof body.
The proof constructs finite-free exactness/product preservation, degreewise balanced
cokernel isomorphisms, their strictly natural tower comparison, the actual additive
Roos comparison, and the arithmetic block/selection quasi-isomorphism.
Updated the node's proof route to these constructions. Public statements, definitions
and public imports are unchanged. Change record:
`coord/changes/D3-finite-free-quotient-roos-import-repair.md`.

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.PrincipalQuotientCompletion.finiteFreeQuotientRoosComparison`
(node `lem-pur-finite-free-quotient-roos-comparison`).
Zero holes remain in the item. Zero holes added; zero statements split off.
Every private helper is proved or concretely constructed. Finite rank zero is
included by the empty finite biproduct; the positive arithmetic exponent ensures
strict monotonicity of `n ↦ e * (n + 1) - 1`.

## No longer needed

Removed H8's private import of
`Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion` and the proof dependency
`lem-weil-completed-integral-principal-unit-criterion`. Its two elementary tensor
identities are now proved locally, without its specialized coefficient machinery.

The original planned `lem-sfb-finite-free-scalar-coordinates`
(`Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`) is unnecessary: the proved
private tensor finite-power and conservative restriction lemmas of
`Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport` apply directly to the module
categories with independent universes.

The original planned `lem-pur-roos-additive-comparison`
(`Sheaf.CategoryTheory.RoosAdditiveComparison`) and
`lem-weil-strict-roos-comparison` (`Sheaf.CategoryTheory.StrictRoosComparison`)
are unnecessary: `Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence` gives
the actual cone comparison, its coordinates, naturality and invertibility directly.
The theorem from `lem-sp-strict-tower-arithmetic-restriction`
(`Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`) is unnecessary:
`Sheaf.CategoryTheory.CofinalRoosRestriction` supplies the stronger explicit cochain
quasi-isomorphism. The public definitions import
`Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs` stays, and the
statement dependency on the arithmetic node remains.
No module or declaration is withdrawn. These are unused dependencies of this proof,
not claims that they have no other consumers. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The H8 proof itself was complete, but its private import changed global instance
state transitively. The red-build note identifies the resulting failure in
`WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights`. This repair removes that
import entirely, rather than adapting the unrelated consumer. The historical
consumer was restored during this session and remains unchanged by this delivery.
The refreshed source tree has 2,042 transitive consumers; declaration consumers
are listed with their holders in the change record. The item's signature and structure are unchanged.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
