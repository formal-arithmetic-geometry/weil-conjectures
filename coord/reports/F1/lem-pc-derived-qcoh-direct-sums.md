# Stage-1 report: lem-pc-derived-qcoh-direct-sums

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-derived-qcoh-direct-sums.json`: statement node split into three proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-ambient-direct-sums.json`: one statement-only prerequisite; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None.

## WANTED

WANTED: `literature/stacks-project/derived-categories-of-schemes.tex`, proof of `perfect-lemma-quasi-coherence-direct-sums` and cited `Injectives, Lemma injectives-lemma-derived-products`, for `lem-pc-derived-qcoh-direct-sums` and `lem-pc-derived-ambient-direct-sums`.

## What was checked and corrected

The imported item had the correct Stacks statement but no proof, and its Mathlib search records did not match the required search log. I reran the item searches with `msearch.py` (LeanSearch unavailable, LeanFinder and Loogle found no direct theorem, and Mathlib grep found no derived quasi-coherent direct-sum theorem) and replaced the records with the actual queries and results. I searched the whole DAG and blueprint for direct-sum and derived-category statements. The existing binary quasi-coherent sum node and directed-colimit node cover the quasi-coherence closure argument, so I did not create duplicate nodes.

## Review by F1

I read the item, `def-pc-derived-category`, the existing binary quasi-coherent direct-sum node, and the existing directed-colimit quasi-coherent node. Step 1 cites the new ambient statement, whose wording explicitly supplies both the termwise construction and the cohomology identity used. Step 2 uses the definition's full-subcategory condition, then checks the finite-subset filtered system: finite sums use the existing binary statement and its hypotheses (scheme and quasi-coherent modules), while the directed-colimit node states that a directed colimit of quasi-coherent modules is quasi-coherent. Step 3 uses the same full-subcategory statement and the ambient universal property. I verified the empty family separately (the zero sheaf and zero complex) and the singleton family (the canonical identity direct sum). The new prerequisite is statement-only because it is the cited general derived-products theorem; it was searched independently in LeanFinder, Loogle, and Mathlib grep, with LeanSearch recorded as unavailable. Every citation quote in `citations.json` is copied verbatim from the cited node statement.

The route checker identified the two existing quasi-coherent module lemmas as generic tools from another unit; I declared both in `split_report.tool_uses` with the precise closure facts taken from their statements. Because the imported item is assigned to `sk-thm-picard-duality`, I also recorded its statement and proof-step realization in that unit record, as required by the stage-1 key-node rule.

## What could not be finished

The Stacks source TeX named by the imported node is not present in this checkout, so the exact source text could not be opened locally; the report records it as WANTED. No Lean declaration matching the item or the new prerequisite was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## Second reading by F1

- Item statement: checked against the pinned Stacks `perfect.tex`, Lemma 08DT (`lemma-quasi-coherence-direct-sums`), lines 79-94. Its original quasi-compact and quasi-separated assumptions are absent from the source and were removed. The imported `source` field still names the nonexistent `derived-categories-of-schemes.tex`; it is maintainer-owned delivery metadata, so the corrected file and tag are given in `proof_origin` and the steps.
- Step 1: checked against `perfect.tex` 08DT, proof lines 85-90, and `injectives.tex` 07D9 (`lemma-derived-products`), clauses (1)-(2) and proof lines 2021-2037. The new ambient node states both the derived coproduct and the cohomology identity used here.
- Step 2: checked against `perfect.tex` 08DT, final proof sentence, `lem-weil-pbc-quasi-coherent-module-direct-sum` (01BF/01ID), and `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections` (01ID/01LA). The cited binary node states quasi-coherence of two sums on every scheme; the directed-colimit node states quasi-coherence of the colimit. The step now exhibits the directed set of finite subsets, its empty member and union upper bounds, the zero base case, finite induction, and the coproduct universal-property bijection identifying its colimit with the full sum.
- Step 3: checked against the full-subcategory clause of `def-pc-derived-category` and the ambient coproduct node. The displayed Hom-set bijection restricts unchanged to the full subcategory, so the conclusion follows in a few lines.
- New node `lem-pc-derived-ambient-direct-sums`: checked hypothesis by hypothesis against pinned `injectives.tex` 07D9 and `perfect.tex` 08DT. Every scheme has a Grothendieck abelian category of sheaves of modules, as the paragraph before 07D9 says; 07D9 gives the termwise derived coproduct, and 08DT derives the cohomology identity from exact sums. It is a statement-only, self-contained node with definition links and source labels. Whole-DAG tag and keyword searches, whole-blueprint searches for derived sums and Grothendieck abelian categories, and recorded LeanFinder, Loogle and Mathlib grep searches found no duplicate or exact Mathlib leaf. `HomologicalComplex.hasExactColimitsOfShape` covers complexes, not this derived-category result.
- Small cases: for the empty scheme all module sheaves and complexes are zero; for an affine scheme over a field the construction is the usual direct sum of complexes of vector spaces. For an empty index set the finite-subset system has one object, the zero sum; for one index it has empty and singleton subsets and colimit the given sheaf. Degree zero and degree one cohomology both commute with sums by exactness, and no boundedness assumption enters.
- Changes: corrected the item's extra hypotheses and TeX; replaced the invented source filename in the proof metadata and new node with the pinned `perfect.tex`/`injectives.tex` labels; expanded Steps 2-3 where the finite-colimit and full-subcategory arguments had been compressed; updated citation quotes and recorded independent Mathlib searches. The first worker's `WANTED` note was true of the checkout at that time; the pinned TeX was read from the recorded upstream commit for this second reading.
