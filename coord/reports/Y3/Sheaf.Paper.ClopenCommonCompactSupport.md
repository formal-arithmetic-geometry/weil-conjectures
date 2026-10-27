## What changed

Reduced `clopenSupport_insertion` to the general finite-product adjunction theorem
`clopenProductAdjoints`. The item now constructs the actual intrinsic derived
restriction equivalence from the ordinary clopen equivalence and exact termwise
localization, applies the generic categorical result, and checks the prescribed
open unit. Its triangulatedness clause follows from exactness. Its constructibility
clause is proved from diagonal invertibility, off-diagonal zero, and
`finite_clopen_constructibility_bounds`, retaining the original cohomological bounds.
All original public signatures and definitions are unchanged.

The implementation uses proved private helpers in the item and a single new module,
`Sheaf.Paper.ClopenProductAdjoints`, for the remaining purely categorical obligation.
The generic derived-category instance exposed by private imports is disabled in the
local proof context, following `FiniteClopenConstructibilityBounds`.

## Proved and sorry left

Closed the original body of `WeilConjectures.PurityFiniteSetting.clopenSupport_insertion`
by reduction, adding one strict general categorical subproblem. This is a decomposition,
not a net hole reduction: one original hole closed, one new hole added.

The remaining holes are:

- `WeilConjectures.PurityFiniteSetting.clopenSupport_independent`, unchanged, node
  `lem-pur-clopen-common-compact-support`.
- `clopenProductAdjoints`, added, node `lem-pur-clopen-product-adjoints`.

No definition contains `sorry`. The final item compiled cleanly in 49.9 seconds; the generic categorical module compiled in 1.6 seconds.

## No longer needed

No original declaration, node, module, or public import is withdrawn. The original
unit route remains. The abandoned direct coordinate-adjunction implementation and
scratch modules are not part of the delivery. No original proof dependency is claimed
as pruned, since other clauses of the module still use the original imports.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan's elementary finite-product step is
larger in Lean than its wording suggests: it must normalize the right adjunction against
a specified left adjunction and identify the precise biproduct map of units. The new
node records exactly that categorical argument. Empty index types and empty components
are retained; no nonemptiness or separatedness hypothesis was added.

## New nodes

`lem-pur-clopen-product-adjoints` is the finite-product category calculation from
steps 4-5 of the original node. It is independent of schemes, coefficient rings,
derived localization, triangulatedness, and constructibility. The item carries out
those geometric and derived transports in Lean. The new theorem is strictly a part
of the insertion argument, not a renaming of the scheme theorem. No existing statement
or definition changed, so no change record is required.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
