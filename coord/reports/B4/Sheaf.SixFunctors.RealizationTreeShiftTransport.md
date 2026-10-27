## What changed

Replaced the body of `realizationTreeShiftTransport` by a complete Lean combination
of two strictly smaller tree-induction obligations, with the original theorem type
unchanged. This is a decomposition, not a complete proof of the mathematics.

The written proof forgets the selected-generator predicate by induction, uses
`SynchronizedPair.components` and `Realizations.coherence` to prove both actual
intertwining equations, maps the system square through total limit using naturality
of its designated shift, and cancels invertible realization components to prove the
integral square. An induction on the ordered list of input changes proves the last
conclusion. That induction works for arbitrary lists, including repeated labels;
the public theorem keeps its original distinct-label premise.

Extracted the eleven existing data declarations verbatim into
`Sheaf.SixFunctors.RealizationTreeShiftData`, publicly re-exported by the item, so the
lower context theorem can use the selected relation without an import cycle. All
original public imports remain. The data module directly imports the existing
GeneratorReductionData provider of inverseOrZero, which its generator-law
definition uses. Change record:
`coord/changes/B4-realization-tree-shift-data.md`. No other existing Lean module changes.
There are no current downstream Lean importers according to `tools/downstream.py`.
The DAG parents and the unit route remain.

Validation: the data and both lower theorem modules compiled through `lcompile.py --all`.
After correcting an associativity normalization and the explicit empty-list type
conversion, the item compiled without errors or warnings in 6.3 seconds. The
first delivery attempt compiled the earlier version and pushed nothing; the
corrected packet is submitted again for all mandatory delivery checks.

## Proved and sorry left

Original item: one hole, in
`WeilConjectures.IntegralSystemRealization.realizationTreeShiftTransport`.
That body now contains no `sorry`; its combination proof is complete.

Added two holes, one per new module:

- `WeilConjectures.IntegralSystemRealization.realizationTreeSingleShift`
  (`lem-pur-realization-tree-single-shift`): original proof steps 1--4, domain
  stability and the single-leaf expression realization square. It assumes no
  generator predicate and concludes no map-context or finite-list result.
- `WeilConjectures.IntegralSystemRealization.realizationTreeSystemSquare`
  (`lem-pur-realization-tree-system-square`): original proof step 7, the system
  square under selected contexts. It assumes both updated domains, uses no
  insertion or realization-recursion hypothesis, and concludes no integral
  square, intertwining equation, domain existence or finite-list result.

Thus one original hole was reduced to two lower holes (net +1); this is counted
as a decomposition. The extracted definitions contain zero holes. The three
private helper theorems in the item are completely proved.

## No longer needed

Removed these private imports from the item:
`Sheaf.Paper.SfIntegralConstructibleTriangulated`,
`Sheaf.Paper.NormalizedDVRTower`,
`Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`,
`Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift`, and
`Sheaf.SixFunctors.IntegralSystemExpressionDomain`.
The item's combination proof does not use them. The first four mathematical
obligations are retained in the single-leaf node's proof dependencies, and the
expression domain remains a statement prerequisite through the public data.
These modules are not claimed globally pruned. Commutation of distinct dependent
updates is also unnecessary for the ordered-list conclusion: its proof follows
the recursive definitions without rearranging updates or combining shifts.

Disposition of the original declared proof dependencies:

| node | use after decomposition |
|---|---|
| lem-weil-integral-constructible-triangulated | Single-leaf domain induction; no direct use in the combination. |
| def-coef-normalized-dvr-tower | Single-leaf domain induction; no direct use in the combination. |
| def-weil-pbc-etale-origin-witness | Single-leaf domain induction; no direct use in the combination. |
| lem-weil-proetale-tor-interval-shift | Single-leaf domain induction; no direct use in the combination. |
| def-pur-integral-operation-shift-data | Fixed total-limit shift naturality in the combination and both lower inductions. |
| def-sf-integral-system-expression-domain | Domain witnesses in the extracted data and both lower inductions. |
| def-pur-integral-expression-occurrences | Independent slot/context induction in the lower theorems and extracted data. |
| lem-pur-integral-realization-recursion | Single-leaf comparison induction; no direct use in the combination. |
| def-pur-synchronized-canonical-maps | Direct projection to both canonical-pair components. |

No DAG dependency is globally unnecessary: the original domain and selected-path
arguments are now assigned to the two lower nodes. Original proof steps 5--6 do
not need to reconstruct realization intertwining: it is already exactly the
`Realizations.coherence` field, reached through the existing canonical-pair
projection. No new contextual-intertwining dependency is imported. No module is
withdrawn, and no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. `Recursion.BasicTree` excludes compact-support symbols;
the lower single-leaf proof explicitly expands those symbols and uses the canonical
supportExpansion coherence equation before applying the assumed recursion. The
old proof plan spent work deriving intertwining
that the realization structure already supplies. The public data had to be
placed below its two tree-induction lemmas to avoid a module cycle; this changes
its location only. Searches of Mathlib, the source library and Sheaf found generic
shift naturality APIs but no existing selected-context or single-leaf realization
theorem that closes the two remaining induction obligations.

Edge checks: the empty update list is identity; the cons argument uses the actual
sequentially updated family. Zero and negative shifts use the same map/cancellation
proofs. Repeated labels also satisfy the ordered-list conclusion. The system
context obligation retains its selected basic-generator predicate, the precise
tensor side and the intermediate independence/admissibility witnesses. It does
not assume that finite evaluation detects equality of system maps.

## New nodes

`def-pur-realization-tree-shift-data`: attaches the existing constructions to the
new data-only module, preserving every body and signature.

`lem-pur-realization-tree-single-shift`: the domain-stability and one-leaf
realization induction, exactly original steps 1--4, with its complete natural
language proof in both the node and theorem docstring.

`lem-pur-realization-tree-system-square`: the selected-generator system-square
context induction, exactly original step 7, with its complete natural language
proof in both the node and theorem docstring.

All use the coefficient-comparison and inherited-equations sentences of the
current blueprint as motivation and retain agent proof provenance. LeanSearch,
LeanFinder, Loogle and source/library grep searches are recorded. The mathematical
source does not itself assert the conditional shift theorem.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
