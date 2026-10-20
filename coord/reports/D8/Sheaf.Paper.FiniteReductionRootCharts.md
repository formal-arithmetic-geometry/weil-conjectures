## What changed

Completed all three proof holes of `Sheaf.Paper.FiniteReductionRootCharts`.

- `finiteReduction_preserves_ctf` applies the existing
  `ProEtale.scalarExtensionFunctor_preserves_constructible_tor` to the actual quotient
  homomorphism. Its only new proof import is `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`.
- `existsUnique_finiteReductionRootTrivialization` constructs the forward linear sheaf
  map on constant sections and its inverse by extension/restriction of scalars. Both
  inverse identities and uniqueness are proved using sheafification. The private generic
  helper takes explicit existing sheafification instances to avoid repeated expensive
  instance synthesis.
- `existsUnique_finiteReductionFixedChart` uses the actual ordered three-factor composite.
  `finiteReductionChartComposite` caches that construction at an abstract coefficient ring.
  The normalization predicate is represented by exact heterogeneous equality with this
  composite; `finiteReductionChartComposite_normalized` proves its equivalence to the
  original three-factor existential normalization, including the middle root-chart factor.

The definition representation change is recorded in
`coord/changes/finite-reduction-chart-normalization.md`. The original normalization with
an application of the generic equivalence was also tested and still exceeds 60 seconds;
the cached equivalent definition avoids that conversion. The node records the actual route.
No target signature changes. No new statement is left unproved.

## Proved and sorry left

Closed all three original holes:

- `WeilConjectures.PurityFiniteSetting.finiteReduction_preserves_ctf`;
- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionRootTrivialization`;
- `WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionFixedChart`.

All belong to node `def-pur-finite-reduction-root-charts`. Holes left: zero.
Holes added: zero. Split off: zero. The complete module compiled with `lcompile.py`
in 23.1 seconds with no diagnostics on the final continuation. Imported theorems retain their existing proof status;
no claim is made to close their holes.

## No longer needed

No imports were removed. No whole module or node has become unreachable. The existing scalar-extension theorem
supplies finite-Tor preservation, so no new flat-model or stratum lemmas are introduced.
The source node had no numbered proof plan and no proof dependencies before this delivery.

## Where the brief, the DAG or earlier work was wrong

Earlier reports described unverified drafts and omitted the normalization change.
The completed module uses explicit existing sheafification instances in the private
root-line helper to avoid repeated synthesis. The original three-factor normalization
also incurred an expensive conversion; the equivalent cached normalization has a proved
generic equivalence and unchanged factors and endpoints. Some compile attempts timed out;
the latest complete-module check compiled cleanly in 23.1 seconds. The downstream scan
was repeated against current sources: 156 importers, with the normalization predicate
referenced only in this module. No consumer adaptation is needed.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
