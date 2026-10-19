## Worker report

Item: `lem-coef-simplicial-arrow-attachment-localization` (Q04), repaired after the return entry C1/C4/E1. I retained the item statement and its HTT route, added one strictly smaller statement-only interface for the missing ordinary-to-derived comparison, rewired the dependent steps, and updated the verbatim citation list. No Lean, compiler, Lake, live-project, or launcher file was written or run.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-strict-pushout-derived-comparison.json`: new statement-only node; Mathlib verdict no match.
- `dag/nodes/sec-six-functors/lem-coef-simplicial-arrow-attachment-localization.json`: repaired steps 2, 3 and 5, proof dependency union, and split summary; statement unchanged.
- `citations.json`: added the new node's verbatim statement quote for steps 2, 3 and 5.
- `report.md`: this report.

New nodes: 1. Mathlib leaves: 0.

## Attachments

None. No finished declaration for the item or the new node was found in the permitted source trees.

## WANTED

WANTED: archival copy of Jacob Lurie, *Higher Topos Theory*, Appendix A.3.5, especially Proposition A.3.5.5, for the item and the new comparison node. I read the Harvard PDF online on 2026-10-17 (printed pp.891--893; PDF pp.908--910); it is absent from `literature/`, so both statements remain agent-sourced interfaces to that result.

## What was wrong and what changed

The returned split cited `lem-coef-simplicial-derived-pushout-mapping` as if its cofibrant-replacement mapping formula proved that the strict pushout with arbitrary `D` was already derived. Its statement does not say that. I added `lem-coef-simplicial-strict-pushout-derived-comparison`, whose hypotheses are exactly the cofibrant walking-arrow factorization and an arbitrary labelled `D`, and whose conclusion is the ordinary-to-derived comparison in `h sCat`, including repeated labels and the empty family. This node has no dependency on the item or on the rejected left-properness route. Steps 2 and 3 now invoke it before using framed mapping comparisons; Step 5 explicitly carries it through the identifications with `L_V D`. The proof-dependency union and all citation quotes were updated. Whole-DAG and whole-blueprint searches found no duplicate or more general existing node; the three required Mathlib search kinds were run for the new node and found no match.

## Review by Q04

I read the item's HTT source places (Notation A.3.5.1, Remark A.3.5.2 and Proposition A.3.5.5) and the full statements of every cited node. The item statement still has small simplicial categories, the cofibration/Dwyer--Kan factorization, arbitrary label set, ordinary pushout, functoriality, common-label invariance, and identity-collapse extension with no extra fibrancy or cofibrancy hypothesis.

Step 1 uses the inversion-universal-property, interval-lifting, and lifting-class-closure statements for the factorization, cofibrancy, coproduct cofibration, and existence of the displayed pushouts. Step 2 uses the new node for the exact ordinary-to-derived comparison for arbitrary `D`, then uses the derived-pushout mapping node for the function-complex formula; the interval-lifting citation supplies the model context. Step 3 uses the new node for both strict pushouts, the derived-pushout mapping node for homotopy pullbacks and coproducts, and the inversion-universal-property node for the localization characterization. Step 4 is the elementary pushout universal-property argument. Step 5 uses the inversion-universal-property node for the restricted Hom bijection and the new comparison node to transport the result from `L_V D` to the strict pushout. Step 6 is the elementary pushout construction of the identity-collapse extension.

I checked the new statement on `V=∅`, a singleton, repeated labels, coincident endpoints, and an arbitrary noncofibrant `D`; its conclusion is exactly the strict-localization comparison supplied by HTT A.3.5.5. I checked that no step invokes left properness or a cofibrancy hypothesis on `D`, and that every cited quote in `citations.json` is verbatim. The new node is strictly smaller than the item: it gives only the ordinary-to-derived comparison and no localization universal property, invariance, or extension clause. No SGA source is used, and no proof step exceeds 2,000 characters.

## Validation

Remote `check_dag` passed after adding the required chapter and unit metadata to the new node. Remote `review_split` passed with one new node and an agent-written proof. The first dry run then rejected only because the new node's recorded Mathlib query text did not exactly match the `msearch.py` log; I reran all three searches verbatim, updated `mathlib_searches`, and the corrected dry run passed: `OK (not pushed) deliver/Q04/lem-coef-simplicial-arrow-attachment-localization at 0ee3e4ad21: preflight passed`.
