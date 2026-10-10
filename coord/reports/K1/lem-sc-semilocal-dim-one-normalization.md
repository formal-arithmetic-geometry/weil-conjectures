Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-semilocal-dim-one-normalization.json` — statement split into three proof steps; 1 new supporting node.
- `dag/nodes/sec-curve-estimates/lem-sc-integral-closure-dedekind-surjective-fibres.json` — statement-only unsplit node; Mathlib searches found no exact match.

Attachments: none.

WANTED: none.

The item was not present in the Lean source: searches for the item id, its blueprint tag, and the normalization/semilocal terminology found no declaration under `WeilConjectures/`. I read the imported item and its source references. The source sentence in Varieties Lemma 09N2 invokes Algebra Lemma 034X, whose full statement is recorded in the new support node (specialized only when used to the fraction-field case). The support node was searched across the DAG and blueprint; no existing node states its Dedekind-plus-finite-fibres conclusion.

## Review by K1

I checked the source text in `/home/ubuntu/c1-stacks-review/algebra.tex` at `lemma-integral-closure-Dedekind` (Stacks Tag 034X) and `/home/ubuntu/c1-stacks-review/varieties.tex` at the proof of `lemma-semi-local-dimension-one-conductor` (Tag 09N2). The support node matches 034X: its hypotheses are a Noetherian one-dimensional domain, its fraction field, a finite extension, and the integral closure; its conclusions are Dedekindness, surjective finite fibres, and maximal-ideal contraction. The item applies it with the extension equal to the original fraction field K.

Step 1 cites exactly the support node for the Dedekind, finite-fibre, and contraction conclusions. Step 2 uses the support node's finite-fibre and contraction clauses: the finitely many maximal ideals of semilocal B give finitely many target fibres, and every maximal ideal upstairs lies in one of them. Step 3 is elementary from the defining inclusions B ⊆ B' ⊆ K: the fraction field of B' contains K because it contains B, and is contained in K because B' is a subring of K. I checked the edge cases B = a DVR and B = a field; the latter is excluded by the dimension-one hypothesis, while the DVR case gives the expected finite set of maximal ideals upstairs.

The Mathlib searches were run for both the item and the new node with LeanFinder, Loogle, and Mathlib grep. LeanFinder returned only results requiring a Dedekind base; Loogle was unavailable; grep found no matching finite-fibre theorem. The new node remains statement-only as required. No source or statement correction was needed.

## Not duplicates

lem-sc-integral-closure-dedekind-surjective-fibres vs lem-sc-semilocal-dim-one-normalization: the new node is the general finite-extension theorem 034X, while the item specializes it to the integral closure in the original fraction field and additionally concludes semilocality.
lem-sc-integral-closure-dedekind-surjective-fibres vs lem-weil-pbc-z-localizations-dvr: the new node concerns integral closures and finite spectrum fibres; the existing node concerns explicit localizations of the integers and their DVR structure.
lem-sc-integral-closure-dedekind-surjective-fibres vs lem-sc-dedekind-localization-dvr: the new node establishes Dedekindness and finite fibres for an integral closure; the existing node establishes that a localization of an already Dedekind domain at a maximal ideal is a DVR.
lem-sc-integral-closure-dedekind-surjective-fibres vs lem-sc-dedekind-intersection-localizations: the new node is the 034X integral-closure theorem; the existing node states intersection and contraction identities for localizations of a semilocal Dedekind domain.
lem-sc-integral-closure-dedekind-surjective-fibres vs lem-sc-semilocal-dedekind-dvr-reduction: the new node constructs a Dedekind integral closure with finite fibres; the existing node reduces an already semilocal Dedekind domain to finitely many DVR localizations and characterizes its Jacobson radical.

## Second reading by K1

- Item statement: checked against Varieties Lemma 09N2 (`lemma-semi-local-dimension-one-conductor`), hypotheses and normalization conclusion; verdict: correct, with the fraction-field conclusion following from the inclusions.
- Step 1: checked against Algebra Lemma 034X and existing leaf `lem-weil-pbc-integral-maximal-contracts-maximal`; verdict: fixed unsupported contraction claim by citing the leaf.
- Step 2: checked the finite union of finite fibres argument against semilocality and both cited statements; verdict: fixed dependencies and citations.
- Step 3: checked fraction-field equality directly from $B\\subseteq B'\\subseteq K$ and `Frac(B)=K`; verdict: elementary and valid.
- Supporting node `lem-sc-integral-closure-dedekind-surjective-fibres`: checked clause by clause against Algebra Lemma 034X; verdict: fixed to Dedekindness, surjective finite fibres, and finite residue-field extensions, removing the extra contraction clause.
- Supporting-node form: checked B1--B7, definitions, source tag/label, statement-only form, and Mathlib search records; verdict: valid after metadata repair.
- Existing-node search: searched `dag/nodes` for integral extensions, finite fibres, lying-over, and maximal contractions; reused `lem-weil-pbc-integral-maximal-contracts-maximal`.
- Blueprint search: `tools/blueprint_refs.py search` found no matching blueprint node; corrected both `blueprint.from.via` lists to omit sibling split nodes.
- Edge cases: checked a DVR base, a field base (excluded by dimension one), and zero/empty cases (excluded by domain and dimension hypotheses).
- Changes made: corrected source labels and `created.item`, repaired the 034X statement, added the maximal-contraction dependency to both steps and `proof_deps`, and synchronized `citations.json` quotes.
