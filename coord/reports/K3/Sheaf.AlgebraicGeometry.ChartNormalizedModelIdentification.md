## What changed

Repaired the returned packet cf3a7b74490. Removed the duplicate private theorems
`AlgebraicGeometry.Etale.comparison_vComp` and
`AlgebraicGeometry.Etale.counitPreservingComparison` from the chart module.

In the unclaimed `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`, exposed
these existing proved helpers in place and factored the existing explicit witness
into `canonicalEtaleCompactSupportNormalization`. The original existence theorem
now wraps that construction. Its statement, all structure fields and existing
public imports remain present. The graph-coherence import becomes public so the
canonical graph core is visible in the new definition body. The public definition
uses public declarations;
its data are the canonical graph core, with no arbitrary witness selection.

The chart proof imports the normalization module explicitly for the new canonical definition.
It proves the two specified comparison equalities by reflexivity. The remaining
retained proof identifies pairwise transport with normalization, identifies the
chart map with the ambient comparison on every unbounded input, and uses the
fixed compositor and cocycle laws for simultaneous model changes. The final
clause uses the existing bounded-below common-refinement compatibility.

Updated both affected nodes from current shared sources, preserving metadata and
changing only owned Lean/proof fields. The change record is
`coord/changes/K3-canonical-etale-normalization-witness.md`; it includes consumer
and holder checks. No adopted source module, target statement or unit route changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.chart_normalized_model_identification`
(node `lem-sp-chart-normalized-model-identification`).

Item holes: 1 before, 0 after. Normalization module holes: 0 before, 0 after.
Holes added: 0. Split off: 0. No sorry remains in either delivered Lean module.
All private helpers in the chart module are proved. Existing imported obligations,
including graph coherence, remain separate existing DAG items.

Validation: both delivered modules passed single-file server compilation in
dependency order (lcompile.py --all, exit code 0). The mandatory delivery
preflight checks the complete packet. The independent maintainer review remains required
for this additive public API repair.

## No longer needed

Removed the duplicate chart helpers `comparison_vComp` and
`counitPreservingComparison`, and its private `chartNormalization` construction.
Their argument is reused from the original normalization module. No module or DAG
node is withdrawn.

Removed direct proof imports of
`Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`,
`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization` and
`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence`. The comparison API is
public through the unbounded comparison import; graph formulas and coherence are
encapsulated in the canonical normalization constructor.

The chart node no longer directly lists
`def-asd-compact-support-graph-comparison`,
`lem-asd-compact-support-graph-sheaf-normalization`, or
`lem-asd-compact-support-graph-coherence` as proof dependencies. Those dependencies
remain needed by the original normalization theorem and are preserved there.

The bounded-below compositor restriction detour is unnecessary: the unbounded
tower and cocycle laws prove the chart equations before restriction. The existing
bounded-below comparison restriction and all source-library declarations remain.

## Where the brief, the DAG or earlier work was wrong

The returned packet copied two word-for-word private lemmas from the existing
normalization module. Its existence theorem alone hides the canonical fields;
repeating its generic helper proofs to recover them was unnecessary. Exposing the
original constructor in place fixes that interface gap and eliminates duplication.

No mathematical statement error was found. The node's chart composition detour
can be shortened to the unbounded natural-transformation computation retained
here. The current blueprint Charts argument and unit sk-lem-sp-reduction remain.
Empty schemes, identity maps, the zero coefficient ring and arbitrary proper
refinements require no added hypotheses.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
