## What changed

Replaced the proof of `AlgebraicGeometry.formal_chart_geometric_regularity` without
changing any binder or conclusion. Its proof applies the existing residual-unit
face decomposition and formal-monoid extension-model theorem, uses the three new
strictly smaller statements below, and proves the intervening completion descent
and final transport in Lean.

The private `regularity_of_model_dimensions` proof constructs the completion-quotient
isomorphism from `AdicCompletion.exists_local_completion_quotient`, descends regularity
using completion regular-iff, rewrites dimensions by completion-dimension, and cancels
the common Boolean dimension drop. Cancellation uses `ENat.WithBot.add_one_cancel`,
so it is valid even before finiteness is invoked. The private `rank_eq_of_mulEquiv`
constructs the group-completion equivalence, its integral linear equivalence and its
rational base change. The final proof constructs the ideal quotient equivalence and
transports regularity and dimensions through it. It also proves directly that the
monomial boundary lies in the maximal ideal.

Moved the eleven notation declarations, with unchanged signatures and bodies, to
`FormalChartGeometricData` and publicly re-exported them. All original public imports
remain. The data node owns the definitions; the original node keeps its exact statement
and now follows the Lean combining proof. Change record:
`coord/changes/formal-chart-geometric-data.md`.

Validation: all five modules compiled individually through lcompile; the current item
compiled without warnings in 7.5 seconds. No direct external importer exists to adapt.
No `sorry` occurs in a definition or in a private proof. The delivered checks additionally
compile the modules with their axiom probes.

## Proved and sorry left

Closed the one original direct hole in
`AlgebraicGeometry.formal_chart_geometric_regularity`
(node `lem-trf-formal-chart-geometric-regularity`). Its combining proof is complete.

Added three public theorem holes, each exactly `:= by sorry`, with source and full
natural-language argument in both its docstring and its new DAG node:

- `AlgebraicGeometry.formal_chart_local_preparation`
  (`lem-trf-formal-chart-local-preparation`): Noetherian strict base, Noetherian tensor
  localization and closed-point prime contraction; no completion assumption.
- `AlgebraicGeometry.extended_formal_model_dimensions`
  (`lem-trf-extended-formal-model-dimensions`): only the completed-pair dimension and
  stratum regularity calculation for a general sharp fs monoid; no geometric stalk.
- `AlgebraicGeometry.formal_chart_strict_comparison`
  (`lem-trf-formal-chart-strict-comparison`): canonical strict-local/chart comparison,
  quotient comparison, regularity ascent implication and dimension preservation;
  no formal-model assumption and no dimension-plus-rank conclusion.

This is a decomposition, not a sorry-free proof of the mathematical theorem:
1 hole closed, 3 holes added, net -2. The item has zero direct holes; the data module
has zero holes; each new statement module has one. Imported existing statement holes
are unchanged. The two new private helpers are fully proved.

## No longer needed

No mathematical node or source-library declaration is withdrawn. The original unit
route is retained. The strict-local tools are still required by the new comparison
node, the Noetherian tools by the preparation node, and the formal dimension theorem
by the completed-dimensions node. These are relocated proof obligations, not claims
that those mathematical results have become unnecessary.

The item no longer directly imports the following proof modules; their roles now
belong to the split statements and their explicitly recorded DAG dependencies:

- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Localization.Submodule`
- `Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance`
- `Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale`
- `Sheaf.RingTheory.FormalMonoidRingDimension`
- `Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
- `WeilConjectures.RingTheory.StrictHenselizationDimension`
- `WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat`
- `WeilConjectures.RingTheory.StrictHenselizationNoetherian`
- `WeilConjectures.RingTheory.StrictHenselizationRegular`
- `WeilConjectures.RingTheory.StrictHenselizationTriples`

The completion-regularity, completion-dimension and local-completion-quotient imports
remain because the item now actually uses their declarations. The new proof imports
are the three split modules, regular-local-localization, ENat arithmetic and tensor
base change. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The DAG's eight prose steps leave
nontrivial interface glue: its formal dimension theorem uses the completion of D[T]
while the extended model uses the zero-variable polynomial presentation, and its
strict-local comparison combines different pointed-neighbourhood constructions.
The new statements isolate these pieces rather than assuming their identifications
by definitional equality. Completion descent and the final rank/ideal transport are
now explicit Lean proofs. No source-tree module is changed.

Edge cases: the preparation uses no log regularity; trivial T and n=0 are allowed;
the mixed coefficient-dimension-zero case is empty because it has no parameter.
The unit characteristic and zero boundary cases use the same quotient and rank
transport. The common drop is cancelled additively, with no truncated subtraction.

## New nodes

`def-trf-formal-chart-geometric-data` records exactly the eleven existing canonical
maps, aliases and model predicates moved to the common data module. It adds no
mathematical assertion and no hole.

`lem-trf-formal-chart-local-preparation` isolates Step 1, with the exact closed lift
and affine-coordinate hypotheses, independently of the formal-model hypotheses.

`lem-trf-extended-formal-model-dimensions` isolates Step 4 for an arbitrary local
completed pair. The rest of Step 5 is fully proved in the item's private helper.

`lem-trf-formal-chart-strict-comparison` isolates Steps 6--8 as comparisons and a
regularity implication, independently of any completed toric model or rank formula.
The final argument uses its ideal and characteristic equations, not just its existence.

All new nodes were searched with LeanSearch, Loogle/LeanFinder and Mathlib grep;
results are copied from the actual search log. The blueprint searches found no exact
standalone duplicate. The shared definition change is recorded in
`coord/changes/formal-chart-geometric-data.md`.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
