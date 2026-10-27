## What changed

Proved `WeilConjectures.PurityFiniteSetting.existsUnique_geometricPuritySource` in
`Sheaf.Paper.FiniteGeometricPurityMate`. The proof uses the existing proved ordinary
root-line power transition, propagates its scalar through the ordered tensor powers,
and cancels the two changed charts across the geometric pullback/shift square.
Primitive-root existence and evaluation of the normalization give existence and
uniqueness. The target chart continues to use gamma(zeta), exactly as specified.

Added proof imports `Sheaf.Paper.FiniteRootLinePowerTransition` and
`Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`. Added two proved private
helpers, including the fixed-scalar version of the tensor-power calculation used
in `finiteReductionSourceTrivialization_power` (implemented here before intrinsic
realization). The theorem retains its existing geometric hypotheses; its proof needs no use
of them, so its unused-section-variable linter is locally disabled. No public
signature, definition body, or existing docstring changed.
Updated the existing node's proof route and proof dependencies.

Validation: final single-file server compile passes without warnings in 42.9 seconds.
The import-direction check confirms that the new proof import creates no cycle.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.PurityFiniteSetting.existsUnique_geometricPuritySource`.

One original hole remains, unchanged:
`WeilConjectures.PurityFiniteSetting.finiteGeometricPurityMate`
(node `lem-pur-finite-geometric-purity-mate`). No holes added or split off.
The exchange invertibility, mate construction, geometric input and purity
invertibility already proved in the source are preserved.

The chart calculation includes degree zero, the zero complex and empty schemes:
it only cancels actual chart isomorphisms, never the scalar c^d. It requires no
unramifiedness hypothesis on the coefficient extension and works at level one.

## No longer needed

None. No existing imports or declarations were removed. No node or module is
withdrawn. The original base-change-factor dependencies remain needed for the
unchanged final theorem; the new source-comparison proof uses only the existing
root-line power transition and elementary ordered tensor/shift calculations.
The six-operations unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing proved root-line power-transition API gives
a direct proof of root independence, without introducing any additional statement
or using the still-unproved uniform source-chart scalar theorem. The generic
ordered-power argument and its application follow the already proved
`FiniteSourceChartPowerTransition` calculation, before its final realization step.

Searches: LeanFinder for smooth purity/geometric Frobenius/counit mates returned
generic conjugate-adjunction lemmas, with no specialized purity result; Loogle
`IsPrimitiveRoot` returned the root-order API. Logged grep found no Mathlib version.
Repository searches found `FiniteRootLinePowerTransition` and
`FiniteSourceChartPowerTransition`, whose signatures and proofs were read and used.
The remaining final theorem needs identification of the published finite etale
base-change factors with these fixed-scalar purity and exceptional-mate coordinates.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
