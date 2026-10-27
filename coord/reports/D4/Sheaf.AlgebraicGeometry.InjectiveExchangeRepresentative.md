## What changed

Complete the zero-hole retirement listed in `coord/retire-items.tsv`: withdraw
`Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` via `deleted.txt`.
Its public theorem and private comparison helpers are no longer needed by any
live source. No other Lean source, quarantine archive, DAG node, definition or
target changes. The change record is
`coord/changes/D4-retire-injective-exchange-representative.md`.

The inventory's sole consumer is the historical quarantine copy of
`Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray`. The independent C-4f264
review and its completed maintenance repair explicitly retired that duplicate;
see `coord/changes/C2-strict-local-derived-exchange-maintenance-20261021.md`.
Its old rework row is closed, and its archive must remain historical evidence.
It is not an active consumer to restore or migrate.

## Proved and sorry left

Retirement repair: proved 0 of 0 original sorries; added 0; split off 0.
The removed `AlgebraicGeometry.Etale.injectiveExchange_representative` had no sorry.
No sorry is left in any delivered source and no new declaration is introduced.

The adopted canonical theorem and its adopted Leray consumer retain their existing
complete proofs. The original-model theorem
`AlgebraicGeometry.Etale.smallModel_injectiveExchange_representative`, node
`lem-weil-pbc-injective-exchange-representative`, retains its complete archived
proof and its current rework assignment. It is not withdrawn or replaced.
A scratch module imported the adopted canonical representative and Leray modules,
checked both declarations, and printed their axioms through `lcompile.py`.
It compiled cleanly in 2.5 seconds on the current compile server. Both axiom lists are exactly
`propext`, `Classical.choice`, and `Quot.sound`; neither reaches `sorryAx`.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` only, including
its four imports of `WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison`,
`WeilConjectures.SixFunctors.BaseChange.Square`,
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison`, and
`WeilConjectures.AlgebraicGeometry.InjectiveExchangeSourceTransport`.
These dependency modules remain needed elsewhere and are not claimed pruned.
No live consumer import needs editing: the full active import scan and
`tools/downstream.py --uses injectiveExchange_representative` both find zero
live downstream modules. The only quarantine importer is the independently
retired historical Leray copy described above; its archive remains unchanged.

No mathematical node is pruned. The representative node's attachment already
names `Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative`.
Its sole DAG parent, `lem-weil-pbc-strict-local-derived-exchange-leray`, already
names the corresponding small-model Leray provider and still cites the
representative node. All statement dependencies, proof dependencies and step
uses remain intact, including those of quarantined parents. The `sk-prop-h2`
unit has neither node among its realized statement or steps; the unit and chapter
routes are unchanged. No node refers to the retired module as its Lean provider.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief omits that this is an explicit retirement with zero holes.
The retirement inventory's consumer count and "same statements" description are
historical. The adopted theorem uses canonical strict localization; the retired
theorem uses the small coordinate-ring colimit model. This delivery does not
identify those scheme models or weaken either statement. The original-model
DAG realization and its genuine quarantined rework sources remain untouched.

The old generic parent archive was explicitly retired by an independent review,
which distinguishes it from the current small-model rework archives. Restoring
that old duplicate or clearing the current small-model Lean attachments would
undo reviewed work. Neither is part of this delivery.

Search before pruning: the refreshed LeanFinder search returned generic derived-category
localization comparisons, injective vanishing, and representative existence lemmas;
the earlier search returned generic pullback adjunction lemmas. Loogle did not index
the project-specific derived-mate factorization; msearch grep returned no matches. Direct source searches found the complete adopted theorem,
its complete Leray consumer, and the separately named original-model realizations.
There is no missing mathematical result to split off.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
