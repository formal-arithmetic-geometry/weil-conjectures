## What changed

Proved `AlgebraicGeometry.Etale.etaleChartLeftCompositor_spec` in
`Sheaf.AlgebraicGeometry.EtaleChartLeftCompositor`, preserving every public declaration,
signature, definition body and public import. Added proved private helpers for horizontal
composition, inversion and pasting of comparison squares, full-faithful cancellation,
normalization compatibility, compositor compatibility, equality transport and the assembled
D+ chart. Naturality is the naturality of the constructed natural isomorphism. Its
compactification compatibility follows by pasting the D+ squares and conjugating by the
endpoint inclusion compatibilities. Updated the node's proof and proof dependencies to this
argument. Removed two unused proof imports.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Etale.etaleChartLeftCompositor_spec`
(node `lem-sf-etale-chart-left-compositor`).

Item holes: 1 before, 0 after. Added holes: 0. Split off: 0.
Every added private helper is proved. No other module is changed. The proof uses the
existing stated normalization and comparison API; it does not claim that all dependencies
are free of sorry.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.

Removed direct proof dependencies and their obsolete tool-use entries:
`lem-weil-pbc-module-sheaves-enough-injectives` and
`lem-weil-pbc-dplus-injective-representative`. The existing D+ functors already carry the
boundedness needed here. These nodes and modules may still be needed elsewhere; this
packet does not withdraw them or assert a whole-target-closure pruning count.
No other imports or nodes are removed. In particular the compact-support comparisons and
immersion normalizations remain necessary, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan's explicit injective resolutions are unnecessary at this node: the
stage-2 definitions already construct the entire chart in D+ and provide its ambient
compatibilities. The substantive remaining obligation is the compactification-change
square. The proof follows the original pasting argument using the recorded declarations.
No statement or definition repair was required. No new nodes were introduced.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
