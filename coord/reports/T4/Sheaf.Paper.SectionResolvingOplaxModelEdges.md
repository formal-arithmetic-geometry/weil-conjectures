## What changed

The item theorem now combines two strictly simpler named subclaims: `section_resolving_oplax_closure` and `section_resolving_oplax_edge_identifications`. The parent proof is complete and imports the two new modules. The subclaims retain the original closure and six-edge proof obligations as named `sorry` theorems for follow-up workers.

## Proved and sorry left

Closed the item theorem `section_resolving_oplax_model_edges` by a real conjunction proof. Added the named holes `section_resolving_oplax_closure` (node `lem-pd-section-resolving-oplax-closure`) and `section_resolving_oplax_edge_identifications` (node `lem-pd-section-resolving-oplax-edge-identifications`). No definition contains `sorry`.

## No longer needed

No planned dependency was removed. The original item imports only its constraint data plus the two split theorem modules; the separate K-flat and pullback imports remain available to the closure child.

## Where the brief, the DAG or earlier work was wrong

The DAG presented the closure and six-edge calculations as one theorem, although they are independent conjuncts with no shared conclusion. No statement was weakened or changed; the decomposition makes each missing calculation a strictly smaller theorem.

## New nodes

`lem-pd-section-resolving-oplax-closure` records the resolving-closure conjunct in `lean/Sheaf/Paper/SectionResolvingOplaxClosure.lean`.

`lem-pd-section-resolving-oplax-edge-identifications` records the six-edge conjunct in `lean/Sheaf/Paper/SectionResolvingOplaxEdgeIdentifications.lean`.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
