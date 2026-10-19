# Stage-1 report: lem-trf-proetale-pullback-stalk-coherence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proetale-pullback-stalk-coherence.json` — item, statement split into five proof steps; no new nodes.
- `citations.json` — verbatim statement quotes for every cited node in every step.

## Attachments

None. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` carrying this item or its blueprint tag.

## WANTED

None.

## Not duplicates

No new node was created, so there are no duplicate pairs to report.

## Review by Q30

I read the imported item, the fixed chapter `sec-trace-formula`, and the source proof of `lem-trf-local-frobenius-conjugacy` in both the main-20261015 and master blueprint snapshots. I also read Stacks `sites.tex` Tags 05V1 and 0F4F and `proetale.tex` Tag 0993, which are the stated point/stalk route. The Lean source search found no declaration or blueprint tag for this item; the existing source has only unrelated ordinary scheme and étale stalk results.

For Step 1 I opened `def-weil-proetale-geometric-stalk`, `def-weil-proetale-inverse-image`, and `prop-weil-pbc-proetale-constant-ring-map`. Their statements give the pointed-neighbourhood colimit, the fibre-product base-change functor, and the constant coefficient isomorphism. I checked that the displayed representative map and its inverse use exactly those objects and that the coefficient action is preserved. For Step 2 I checked the same representative formulas for naturality and the identity morphism; no extra hypothesis is used.

For Step 3 I opened the full statement of `lem-weil-pbc-proetale-derived-pullback-composition`. It supplies the normalized comparison on K-flat complexes, while the inverse-image and stalk statements supply the two colimit maps. I checked the fibre-product reassociation and verified that both composites send a representative to the same germ. For Step 4 I checked directly from the stalk colimit statement that precomposition by a field automorphism preserves pointed-morphism relations, has inverse given by the inverse automorphism, and is A-linear.

For Step 5 I read the exactness and termwise-derived clauses of `def-weil-pbc-proetale-operations` and the full statement of `lem-weil-pbc-localization-universal-property`. Applying the first four steps degreewise gives chain-map equalities; localization carries them to the ordinary derived category. I added that localization node to `stmt_deps` and `proof_deps`, filled the blueprint place and `same_as` reference, and recorded both generic tool uses in `split_report`. No statement was weakened and no new node was needed: creating one would restate a clause of this item.

The four msearch queries required for the item were run. LeanFinder, Loogle, and grep returned only ordinary topological/étale stalk or underived pullback declarations; LeanSearch was unavailable on the first attempt and returned the same ordinary stalk results on the retry. These results are retained in the item’s search log.
