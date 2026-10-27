## What changed

Prove `WeilConjectures.PurityFiniteSetting.finiteReductionUnitComparison_isIso`
without changing any public signature or definition. Add the proof-only import
`Sheaf.Paper.ScalarExtensionBinaryCoherence` and private proved helpers for the
ordinary multiplication isomorphism, its section normalization, K-flatness of
the degree-zero unit, and compatibility of ordinary and derived adjunctions on
single complexes. Update the node's proof route to record these steps.

The ordinary multiplication isomorphism and its pure-section formula are used
as tools from `lem-sp-scalar-extension-binary-coherence`. The existing normalized
scalar adjunction and universal K-flat counit in
`def-weil-pbc-bounded-constructible-tower` supply the derived computation. The
argument uses actual tensor multiplication and the specified adjunct, including
when the ring sheaf is zero; it does not choose an arbitrary endpoint isomorphism.

## Proved and sorry left

Closed one of the item's two holes:
`WeilConjectures.PurityFiniteSetting.finiteReductionUnitComparison_isIso`.
No holes added and no statements split off.

One hole remains unchanged:
`WeilConjectures.PurityFiniteSetting.finiteReductionExceptionalComparison_isIso`,
node `def-pur-finite-reduction-comparisons`.
All previously completed source-chart, compact-support and exceptional-existence
proofs are retained.

## No longer needed

None. No imports, modules or nodes withdrawn. The existing declared dependencies
are still used by the other comparison constructions and their proofs.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement discrepancy found. The node's last proof step listed
both isomorphism obligations as unfinished; the unit obligation is now proved.
The exceptional isomorphism obligation remains. The unit's blueprint route is
preserved: compute normalized coefficient change on the flat rank-one unit.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
