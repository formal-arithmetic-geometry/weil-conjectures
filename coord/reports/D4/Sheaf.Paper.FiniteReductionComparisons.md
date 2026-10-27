## What changed

Reduced `WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionSourceComparison`
in `Sheaf.Paper.FiniteReductionComparisons`. The proof constructs a primitive root using
Mathlib, obtains the compatible root by powering, constructs the comparison explicitly,
uses chart independence for its normalization, and proves uniqueness by cancelling a chart.
Added the private proof imports `Sheaf.Paper.FiniteReductionSourceChartIndependence` and
`Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`. Existing signatures, definitions,
public imports and the unit route are unchanged. The item and new node record this route.

The item compiled cleanly through lcompile.py (44.5 seconds). The new helper also compiled.
The helper is a genuine coordinate-change step: it assumes an arbitrary already supplied
untwisted comparison and asserts invariance of its conjugate. It constructs no comparison
and asserts neither existence nor uniqueness of a normalized comparison. The upper proof
supplies these steps. This is a decomposition, not a net hole closure.

## Proved and sorry left

Upper hole closed by decomposition:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionSourceComparison`
(node `def-pur-finite-reduction-comparisons`).

One new hole:
`WeilConjectures.PurityFiniteSetting.finiteReductionSourceChart_independent`
(node `lem-pur-finite-reduction-source-chart-independence`).

Two pre-existing holes left untouched in the assigned module:
`WeilConjectures.PurityFiniteSetting.finiteReductionUnitComparison_isIso` and
`WeilConjectures.PurityFiniteSetting.finiteReductionExceptionalComparison_isIso`
(both node `def-pur-finite-reduction-comparisons`). Their original full proof docstrings
remain in place. The brief explicitly permits reducing one hole while leaving others.
Original item: 3 holes. Delivered item: 2 holes. Added elsewhere: 1 hole. Net reduction: 0.

## No longer needed

None. No existing imports, nodes or modules are pruned. Root charts, the actual pullback
comparison and its shift remain necessary. The finite compact-support scalar comparison
and the transported counit proof remain unchanged. The new helper imports only the root-chart
module; it does not import the assigned module or the finite-exceptional theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The current node grouped the three remaining obligations into
one final proof step; its copy now records the source-comparison construction separately.
A direct search of Mathlib and both project roots found primitive-root and scalar-adjunction
APIs but no root-chart independence theorem. The blueprint search for root charts returned
no duplicate node. The new obligation includes d=0, equal levels, zero objects and empty
schemes: its proof uses scalar naturality and cancellation, with no quotient-flatness or
boundedness assumption. The scalar-unit and exceptional comparison theorems in the library
use different coefficient/realization interfaces, so no unproved identification was used.

## New nodes

`lem-pur-finite-reduction-source-chart-independence`, in
`Sheaf.Paper.FiniteReductionSourceChartIndependence`, isolates the change of primitive-root
coordinates in Step 2 of the current finite-reduction blueprint proof. Its docstring and
node give the integer-scalar cancellation argument and its edge cases. Three actual searches
are recorded. No existing interface is changed and no consumer adaptations are required.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
