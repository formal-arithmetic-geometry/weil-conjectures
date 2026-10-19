# Worker report: lem-coef-derived-restriction-rectification

## Files written

- `lem-coef-derived-restriction-rectification.json`: statement node, split with five proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim citations for every proof-step dependency.
- `report.md`: this report.

## Attachments

None. I searched the slopmaster2 project for the blueprint tag and for the relevant derived-restriction, coherent-evaluation, and covariant-unstraightening names; no sorry-free declaration states this item exactly.

## WANTED

- WANTED: Lurie, *Higher Topos Theory*, Proposition 4.2.4.4 and Appendix A.3.3/A.3.4, for the enriched projective-diagram evaluation comparison and its restriction naturality (the cited IAS PDF is not archived under `literature/`).
- WANTED: Lurie, *Higher Topos Theory*, Proposition 2.2.1.1 and Remarks 2.2.2.11–2.2.2.12, for the covariant unstraightening presentation and base change (the cited IAS PDF is not archived under `literature/`).

## What was checked and corrected

The imported item had an empty proof and stale creation metadata from another group. I retained its statement, source, statement dependencies, and import flags, replaced the empty proof with the projective-factorization, localized-evaluation, coherence, and covariant-unstraightening argument, corrected `created` to Q34, and filled the blueprint ancestry and split report. No statement correction was needed. No new node was introduced: the localized evaluation/restriction node already supplies the derived restriction and coherent comparison, while the right-fibration presentation already supplies covariant base change and preservation of objectwise weak equivalences.

## Review by Q34

I read the item, `sk-prop-sf-biduality-general`, and `sec-six-functors`, then read the full statements of `lem-coef-simplicial-projective-model-calculus`, `lem-coef-kan-diagram-localized-evaluation`, `lem-coef-kan-diagram-evaluation-restriction`, `lem-coef-enriched-diagram-rectification`, `lem-coef-simplicial-right-fibration-presentation`, and `def-cbc-enhanced-diagrams-cones`. Step 1 uses exactly the projective node's objectwise weak-equivalence/fibration clause and its evaluation-to-bifibrant-values clause; these give bifibrant values of F and D and projective fibrancy of D. Step 2 uses the same projective model structure: the cofibration makes QD cofibrant, the composite of the replacement fibration with D→* makes QD fibrant, and objectwise weak equivalence gives the required comparison. Step 3 uses the localized-evaluation node's factorization through E_K, its replacement-equivalence assertion, and its exact restriction identity; the enriched-rectification node identifies E_K on projectively bifibrant diagrams with Φ_K and records vertices, arrows, and coherent compositions. Step 4 uses the explicit all-higher-simplices coherence clause and the enhanced-diagram definition, so the claimed naturality includes transformations and compositions rather than only objectwise values. Step 5 uses the covariant half of the right-fibration presentation: objectwise weak equivalences of Kan-valued diagrams become equivalences of left fibrations, and the base-change isomorphism identifies U_B^cov(D) with u^*U_A^cov(F). I checked that QD and D are objectwise Kan before applying these clauses, and checked empty A or B and identity u as edge cases; the argument still applies. The Mathlib searches were rerun for the item under Q34 (LeanSearch, LeanFinder, Loogle, and Mathlib grep, with a second phrasing); the hits were ordinary nerve, projective-resolution, and evaluation lemmas and none states this derived coherent theorem. No duplicate or source error was found, and the five steps are each below the long-step review threshold.
