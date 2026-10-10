# Stage 1 report: lem-sc-zariski-dimension-bound

## Files written

- `dag/nodes/sec-smooth-purity/lem-sc-zariski-dimension-bound.json`: item, split with no new nodes.
- `citations.json`: verbatim statements used by step 1.

## Attachments

None. The source checkouts contain no sorry-free declaration tagged `lem-sc-zariski-dimension-bound`.

## WANTED

None.

## What was wrong in the imported node

The imported five-paragraph generic-point proof used several substantial uncited facts (support filtrations, dimension drop for closed subsets, exact closed pushforward, and the long exact sequence), and its first paragraph was not a complete argument. The DAG already contains the stronger theorem `lem-sc-noetherian-topological-cohomology-vanishing`, which is the Stacks Proposition 02UZ proof for arbitrary abelian sheaves on Noetherian topological spaces. I replaced the incomplete route with its direct specialization to the underlying topological space of a Noetherian scheme. The Zariski-site definition states that objects are open subschemes with jointly surjective open covers, and the cohomology definition is derived global sections, so the specialization uses precisely the cited statements.

## Review by J1

I read the item node, the unit `sk-prop-sf-cbc`, the chapter record, and the complete existing node `lem-sc-noetherian-topological-cohomology-vanishing`. Its hypotheses are Noetherianity, finite topological dimension, and an arbitrary abelian sheaf; these match the item after forgetting the scheme structure. I also read `def-sc-zariski-site` and `def-sc-zariski-cohomology`: the former supplies the open-subset site and coverings, and the latter defines the cohomology as the derived global-sections groups used by the topological theorem. Step 1 cites each statement for exactly that content; no fact is hidden as an uncited lemma. I searched the whole DAG and blueprint for duplicates before deciding that no child node was needed: the existing topological theorem is the general statement, while the item is its scheme-site specialization. I tested the specialization on an empty scheme and on a zero-dimensional affine scheme; both give the expected vanishing ranges. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; only generic derived-category declarations appeared, and LeanSearch was unavailable, which is recorded as such. The off-unit theorem is declared as a tool use because this compact-support unit has no separate route for Grothendieck vanishing.

## Second reading by J1

- Item statement: checked against Stacks Proposition 02UZ, label `proposition-vanishing-Noetherian`; the Noetherian underlying space, finite dimension bound, arbitrary abelian sheaf, and vanishing range agree as the Zariski-site specialization.
- Step 1: checked each use against `def-sc-zariski-site`, `def-sc-zariski-cohomology`, and `lem-sc-noetherian-topological-cohomology-vanishing`; these statements provide the open site, derived global sections, and vanishing for every abelian sheaf. The specialization is direct, with no hidden induction or support argument.
- New nodes: none; the existing topological theorem was checked for duplication and is used as the generic tool rather than recreated here.
- Edge cases: the empty scheme and a zero-dimensional affine scheme give the expected vacuous higher-degree vanishing; the dimension-one case specializes with `q > d` exactly as in 02UZ.
- Mathlib searches: the recorded grep, Loogle, LeanFinder, and unavailable LeanSearch runs were checked against `searches.jsonl`; no exact Mathlib declaration was found.
- Changed the item source to Stacks `cohomology.tex`, Proposition 02UZ, and set `blueprint.same_as` to `[]`; the prior source was the blueprint file and did not satisfy the source-tag requirement.
