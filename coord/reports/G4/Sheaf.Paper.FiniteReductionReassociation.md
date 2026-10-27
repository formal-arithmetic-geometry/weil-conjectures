## What changed

Proved `WeilConjectures.PurityFiniteSetting.finiteReduction_reassociation` by
transporting `finite_tensor_presentation_reduction` through the specified scalar
realization comparison. Added the proof-only import
`Sheaf.Paper.FiniteTensorPresentationReduction`.

Private proved helpers establish naturality of reassociation, the root charts,
and the chart-normalized source reduction, and cancel the realization units
and counits. The repeated realization calculations are combined into one
abstract categorical lemma; explicit functor associators and local irreducibility
keep the derived constructions from being repeatedly unfolded. The proof uses the independently defined tensor input and source
comparisons without changing any existing definition or public statement.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.PurityFiniteSetting.finiteReduction_reassociation`
(node `lem-pur-finite-reduction-reassociation-intrinsic`).

No holes added; no `sorry` remains in this module. The complete proof compiled
through `lcompile.py` in 59.4 seconds before removing the profiler. The fixed-scalar theorem
`finite_tensor_presentation_reduction` is an existing stated dependency and is
used as such, in accordance with the node's proof plan.

## No longer needed

None. All existing imports and the declared proof dependencies are retained.
No node, module, or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The second step described source-comparison naturality as elementary, but the
comparison is chosen separately at each object using its unique root-chart
normalization. The proof therefore constructs the natural root-chart and
pullback comparison isomorphisms explicitly and identifies their composite
with that unique comparison. This fills in the planned argument without
changing the route.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
