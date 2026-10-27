## What changed

Closed the two exactness holes in
`Sheaf.Paper.CompactSupportScalarLimitFoundations` by decomposing their
conjunctions into strictly smaller component theorems. The tensor theorem now
uses the proved finite-limit and finite-colimit components, the local
all-shaped limit comparison, and the split K-injective component. The
restriction theorem now combines two split components: all-shaped limit
preservation and K-injective preservation.

Added three component modules:

- `Sheaf.Paper.ScalarLimitTensorKInjective`.
- `Sheaf.Paper.ScalarLimitRestrictionLimits`.
- `Sheaf.Paper.ScalarLimitRestrictionKInjective`.

The assigned module's public signatures and definitions are unchanged. The
unused proof-only import
`Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport` was removed.

## Proved and sorry left

The two original holes are closed by decomposition:

- `WeilConjectures.PurStrictScalar.scalarLimitTensor_exact`.
- `WeilConjectures.PurStrictScalar.scalarLimitRestriction_exact`.

Three strictly smaller component obligations remain as named theorem holes:

- `WeilConjectures.PurStrictScalar.scalarTensor_preservesKInjective`.
- `WeilConjectures.PurStrictScalar.scalarRestriction_preservesLimits`.
- `WeilConjectures.PurStrictScalar.scalarRestriction_preservesKInjective`.

Thus this delivery closes 2 original holes and adds 3 split-off holes. No
definition or private declaration contains a `sorry`.

## No longer needed

The assigned proof no longer imports
`Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport`; its transport API is
not used by the completed wiring. The existing finite exactness dependencies
remain in use. The three new component nodes are retained because each is a
strict part of one parent conjunction and is still required by that parent.

## Where the brief, the DAG or earlier work was wrong

The prior route assumed an available global all-shaped limit instance for
`constantRestriction`. The current import closure provides finite
restriction exactness but no such instance, so that clause is isolated as the
strictly smaller `scalarRestriction_preservesLimits` theorem. The tensor
all-shaped limit clause is proved directly by the local finite-free coordinate
comparison. No target statement or definition was weakened.

## New nodes

Added
`lem-pur-compact-support-scalar-limit-tensor-kinjective`,
`lem-pur-compact-support-scalar-limit-restriction-kinjective`, and
`lem-pur-compact-support-scalar-limit-restriction-limits` record the three
strict component obligations. The last records the all-shaped
limit-preservation component of `scalarLimitRestriction_exact`. Its Lean declaration is
`WeilConjectures.PurStrictScalar.scalarRestriction_preservesLimits` in
`Sheaf.Paper.ScalarLimitRestrictionLimits`. The two K-injective component
nodes and modules are included in this delivery as the corresponding strictly
smaller obligations.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
