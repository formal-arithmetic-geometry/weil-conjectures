## What changed

Filled `AlgebraicGeometry.Etale.graph_open_etale_composition` in the assigned module,
without changing its statement or any public import. The proof identifies the chosen
open comparison with the etale graph comparison, applies the existing support/sum
compositor, and transports it to the supplied output compactification.

Two new modules contain complete parts of this proof:
`Sheaf.AlgebraicGeometry.EtaleGraphOpenModelComparison` proves the identity-proper
open model comparison, and `Sheaf.AlgebraicGeometry.EtaleOpenSumDerivedAdjunction`
identifies the two specified derived adjunctions. All remaining added helpers are
private and proved. No existing module other than the item is changed.

The monolithic proof compiled, but the delivery probe exceeded 60 seconds. Aligning
the local preadditive instance with graph coherence reduced expensive conversions;
the two complete comparison proofs were then separated so they can be checked
individually. Keeping normalization inside the generic identity-cancellation lemma
reduced the open-model file from 35 seconds to 6.7 seconds (type checking from
27.2 seconds to 0.16 seconds). The three-file compilation passed without Lean errors
or warnings before this final optimization, and the optimized open-model proof also
compiled. No profiling options, transparency overrides, or new holes are retained.
The DAG proof and dependencies follow the final Lean argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.graph_open_etale_composition`
(node `lem-pur-graph-open-etale-composition`).

Also proved `AlgebraicGeometry.Etale.etaleGraphOpenModelComparison` and
`AlgebraicGeometry.Etale.etaleOpenSumDerivedAdjunction` in the two new modules.
No holes added; no `sorry` remains in any delivered module. The proof uses existing
stated dependencies, including `etaleSupportSumCompositor`; this delivery does not
claim those separate obligations have been closed.

## No longer needed

No original import is removed. The redundant direct proof import of
`Sheaf.AlgebraicGeometry.EtaleSupportExchangeRightMate` is unnecessary because the
normalized-mates import already supplies its helper. Graph coherence is imported
by the new open-model module. No existing module or declaration is withdrawn.

The item does not need a new compactification tower or new geometric section-extension
lemmas: the existing support/sum compositor supplies their combined equation. The
original definitions, graph-derived comparison, chosen comparisons, unbounded
comparison coherence and graph coherence remain used. No original named dependency
is pruned globally.

## Where the brief, the DAG or earlier work was wrong

The original proof plan expands graph sections and derives their composition again.
The library already states the general support/sum compositor equation and proves its
counit conjugacy. Specializing these declarations is shorter and avoids another holed
split of the same obligation. The open-model and adjunction-identification steps are
proved here, including identity and empty opens. The unit route and targets are unchanged.

## New nodes

`lem-pur-etale-graph-open-model-comparison` records the proved identity-proper open
model comparison in `Sheaf.AlgebraicGeometry.EtaleGraphOpenModelComparison`. Its
proof uses graph normalization, monicity, exact factorizations and localization.

`lem-pur-etale-open-sum-derived-adjunction` records the proved equality of the specified
derived adjunctions in `Sheaf.AlgebraicGeometry.EtaleOpenSumDerivedAdjunction`. Its
proof compares their units on cochain representatives and cancels exact factorizations.
Neither node contains a hole; no change record is required for these new modules or
for the proof-only change to the assigned module.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
