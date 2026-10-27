## What changed

Completed `AlgebraicGeometry.Etale.cartesian_sum_mate_sheaf_normalization` in
`Sheaf.AlgebraicGeometry.CartesianSumMateSheafNormalization`, preserving its exact statement.
The proof follows the existing two-step plan rather than splitting the obligation again.
Four proved private helpers establish the unit equation for the mate of the specified
left-adjoint comparison, normalize the sum-to-direct-image map under its adjunction,
show graph extension vanishes on disjoint test objects, and prove Cartesian compatibility
of the graph-defined unit.

The geometric proof constructs the canonical isomorphism between the two graph targets
using `pullbackMapComparison` and the two pullback compositors. It checks its effect on
the graph using pullback projections. Its inverse carries the complementary restriction
to a map disjoint from the other graph, so both restrictions agree by `graph_hom_ext`.
Naturality and the adjunction Hom equivalence then give the requested equation.
The argument includes empty test objects and identity squares without extra hypotheses.

Added the private proof import `WeilConjectures.SixFunctors.BaseChange.Etale` for the
restriction description of ordinary base change. Both existing public imports remain.
Updated the item's node proof, proof dependencies and proof origin to describe the actual
calculation. No shared definitions, public declarations, other existing modules, or
consumer interfaces change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.cartesian_sum_mate_sheaf_normalization`
(node `lem-pur-cartesian-sum-mate-sheaf-normalization`).

The item's module has zero remaining `sorry` statements. Added zero holes and zero
split-off statements. All four new helpers are private and fully proved.
The complete proof passed the required remote single-file compiler in 13.8 seconds.
Removed its single unused-simp-argument warning before final delivery checks.
The required delivery preflight checks the final module and all its declarations.

## No longer needed

The proof needs no derived exchange result: removed `def-kun-unbounded-exchange` from
its proof dependencies and proof-step uses, replacing it with the existing ordinary
`def-weil-pbc-underived-exchange`. The original statement-dependency metadata is preserved.
The existing direct-image node records the other explicit input used by the calculation.
No imports were removed, and no modules are withdrawn or claimed globally pruned.
No new intermediate obligations are needed.

## Where the brief, the DAG or earlier work was wrong

The recorded plan cited the unbounded derived exchange node for an ordinary sheaf mate.
Only the ordinary mate calculus and ordinary etale base change are used here. The
mathematical statement and the graph/adjunction route are unchanged; this delivery
provides the concrete calculation previously left as an obligation.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
