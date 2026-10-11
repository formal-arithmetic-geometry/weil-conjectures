# Stage 1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-homotopy-limit-vanishing.json`: split item into the limit Hom-complex argument and its ordinal inverse-limit child.
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-ML-ordinals.json`: statement-only child for Stacks Tag 0AAT; Mathlib searches found no match.
- `citations.json`: verbatim citations for every step/node use.

## Attachments

None. No declaration tagged `(blueprint: lem-pur-kinjective-homotopy-limit-vanishing)` or otherwise stating the item exists in `WeilConjectures/`.

## WANTED

None. The source files used are available in `/home/ubuntu/c1-stacks-review/`.

## Not duplicates

- `lem-pur-kinjective-ML-ordinals` vs `lem-weil-pbc-mittag-leffler-complex-limit-homology`: the new node is an ordinal-indexed inverse system with degreewise maps onto every earlier limit and concludes acyclicity; the existing node concerns a countable inverse system with ML and essentially constant cohomology and proves a specific $H^0$ limit isomorphism.
- `lem-pur-kinjective-ML-ordinals` vs `lem-pc-tower-surjective-lim-acyclic`: the new node is an inverse limit of complexes indexed by an arbitrary ordinal; the existing node is a countable tower of abelian groups and vanishing of higher derived inverse limits.

## Review by H1

I read the item source route in `/home/ubuntu/c1-stacks-review/injectives.tex`, the limit-ordinal paragraph of `lemma-characterize-K-injective`, and the full proof of `lemma-ML-over-ordinals` in `homology.tex` (Tag 0AAT). The item statement already had the right hypotheses: a limit ordinal, a continuous increasing system with monomorphic maps, termwise injective target, and vanishing of every earlier Hom group in every shift. I checked that the first item step uses injectivity exactly for surjective restriction maps and uses the derived-category definition of cohomology to identify the induction hypotheses with acyclicity of the Hom complexes. The second step quotes the new child verbatim and then reads acyclicity as vanishing in every cohomological degree, yielding all shifted Hom groups. I checked the child statement against lines 7861--7872: it preserves the arbitrary ordinal, the acyclicity of each stage, the surjections to the preceding limits in every degree, and the acyclicity conclusion for the total limit. I searched the whole DAG and blueprint; only countable ML/derived-limit results appeared, and both differ in index category and conclusion. Mathlib searches were run for the child with LeanFinder, Loogle, and source grep; they found only generic acyclicity and countable limit projections, so the child remains unsplit.

## What was wrong or incomplete

The imported item had no proof and its limit step depended on an unstated homology lemma. I supplied that missing statement as a separate node rather than treating the transfinite inverse-limit argument as elementary.

## Could not finish

Nothing remains for this stage; the child is intentionally statement-only for a later worker.

## Second reading by H1

- Step 1: checked against `injectives.tex` limit-step proof and Tag 0AAT hypotheses; repaired the compatible-family extension argument and spelled out the cocycle/chain-map and coboundary/null-homotopy identification.
- Step 2: checked against `injectives.tex` limit-step conclusion and Tag 0AAT; verdict correct, with the source place made tag-explicit.
- `lem-pur-kinjective-ML-ordinals`: checked against `homology.tex`, Tag 0AAT, including ordinal indexing, predecessor-limit surjectivity, and acyclicity; repaired its self-contained statement.

Changes: removed incorrect countable-tower and sheaf-complex definition dependencies from the child, defined ordinal inverse systems and acyclicity in the statement, made both source places cite Tag 0AAT, and made Step 1's transfinite compatibility argument explicit.
