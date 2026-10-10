# Delivery report

1. Files written:
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-dim-one-iff-normal.json`: split statement, no Mathlib match.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-valuation-ring-normal.json`: new unsplit support statement for Stacks 00IC; no Mathlib match.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-principal-maximal-dim-one-regular.json`: new unsplit support statement for Stacks 00PD; no exact Mathlib match.
2. Attachments: none.
3. WANTED: none; the Stacks source is present locally.
4. The imported item had an empty proof. I checked the exact statement and proof of Algebra Lemma 00PD (label `lemma-characterize-dvr`, algebra.tex line 29104), and split its two implications. The regular-to-normal implication uses the existing `lem-sc-regular-local-domain` and `lem-sc-regular-dim1-dvr` statements, the latter supplying 00PD (3) to (1), then the new 00IC valuation-ring normality node. The normal-to-regular implication uses the existing 00PD normal-local/DVR statement and the new principal-maximal-dimension-one regularity node. No statement or unit route was changed.
5. Nothing remains unfinished in this item; the two smaller support nodes are intentionally unsplit queue items.

Blueprint search: `tools/blueprint_refs.py search 00PD`, `search 00IC`, `search integrally closed valuation`, and `search principal maximal regular` returned no identical imported blueprint node. `search normal local domain dimension one` found the existing `lem-sc-normal-dim1-dvr`, and `search regular local ring dimension one` found `lem-sc-regular-dim1-dvr`; their one-directional statements are used or are related, but neither states the full equivalence of this item or either new support claim. The item's ancestor is `lem-weil-pbc-normal-constant-generic`; its original blueprint proof, second paragraph, says 'Now O^sh_{Y, ybar} is a normal domain ... the strict henselization of a normal local ring is normal.' These nodes refine the one-dimensional 00PD input reached through the intervening Serre and normality nodes.

## Review by E1

I read Algebra 00PD (`lemma-characterize-dvr`) and 00IC (`lemma-valuation-ring-normal`) in `algebra.tex`, checking the one-dimensional Noetherian local hypotheses against the item and both new statements. The valuation-ring node says domain plus the fraction-field valuation property and concludes integral closedness. The principal-maximal node is the 00PD implication with a nonzero generator. Both are self-contained, unsplit, TeX-correct, and cite their actual definitions. Whole-blueprint searches by tags and concepts found no matching imported statement; the recorded nearest ancestor and proof clause match the path to the normality argument.

Step 1 uses the exact `lem-sc-regular-local-domain` and `lem-sc-regular-dim1-dvr` statements before applying the new valuation-ring node; this supplies the 00PD implication explicitly. Step 2 uses `lem-sc-normal-dim1-dvr` and the principal-maximal node to recover regularity. The only elementary part is combining the two directions. I checked that a dimension-one local ring is not a field, that the maximal generator is nonzero, and that normality includes the domain condition. I sent Step 1 back under C1 because its first version quoted 00PD without citing the existing regular-to-DVR node. The worker added the citation in text, uses, and proof_deps and reran the checks. No A-F issue remains.
