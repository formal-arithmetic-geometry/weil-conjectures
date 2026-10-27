## What changed

Added `Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness` and imported it from the assigned module. The assigned witness theorem now obtains coproducts from `brownHypotheses_structural` and combines them with the new single-object compactness obligation. The original module's disputed witness `sorry` is therefore removed; the unresolved compactness input is isolated in the new theorem.

## Proved and sorry left

The coproduct part of `CategoryTheory.brownHypotheses_arbitraryField_compactness_witness` is proved from `CategoryTheory.brownHypotheses_structural`. The original witness declaration has no `sorry` left. One `sorry` remains in `CategoryTheory.brownHypotheses_arbitraryField_compactness_obligation`, recorded by node `new-sfb-brown-arbitrary-field-compactness-obligation`; this is a strictly simpler single-object compactness statement and is explicitly disputed because the unrestricted arbitrary-field assertion is false.

## No longer needed

No imports were removed. The witness proof no longer uses the witness node's former proof dependencies `a4-brown-finite-field-internal-compactness` and `lem-sfb-brown-integral-ext-criterion`; those modules remain imported because other proved declarations in the assigned module use them. No existing module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The arbitrary-field compactness witness is mathematically false without an additional finiteness or Ext-bound hypothesis, as already recorded by the `STATEMENT-DISPUTED` comments and the Kummer cup-product obstruction in the assigned module. The DAG's former proof route claimed finite-field and integral compactness as if they supplied the arbitrary-field case; the delivery keeps the disputed obligation explicit and proves the independent structural coproduct clause.

## New nodes

`new-sfb-brown-arbitrary-field-compactness-obligation` records the objectwise compactness obligation with an explicit coproduct hypothesis. Its source is the compactness paragraph of `sk-lem-brown-hypotheses.proof.md`; its Lean declaration is in `lean/Sheaf/SixFunctorsBasics/BrownHypothesesArbitraryFieldCompactness.lean`. No change record is needed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
