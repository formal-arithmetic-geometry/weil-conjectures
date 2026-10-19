# Stage-1 report: lem-trf-etale-local-noetherian-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-local-noetherian-descent.json` — statement, split; no Mathlib match.
- `citations.json` — verbatim statement quotations for every proof-step citation.

## Attachments

None. I searched the source library for the item id, its concepts, and the relevant declaration names; no sorry-free project declaration states this item exactly.

## WANTED

None.

## What was wrong in the imported node

The imported item had no proof steps. I supplied the affine restriction and finite affine refinement required by Tag 034C, then wrote the finite-product faithfully-flat ring argument explicitly. The imported Mathlib searches were retained in substance and rerun through the required search command; no exact Mathlib theorem for the etale-cover descent statement was found.

## Review by Q44

I read the item source in Descent Tag 034C (descent.tex lines 4762–4781), the etale-to-fppf fact in Topologies Tag 021N, and the affine refinement fact in Topologies Tag 0218. I also read every cited node statement. Step 1 uses the existing base-change node for preservation of etaleness and joint surjectivity, the affine-refinement leaf for finitely many affine opens inside covering members, and the affine-open locally-Noetherian leaf for Noetherian coordinate rings. The hypotheses match because each original member is locally Noetherian and each refined member is an affine open in it.

Step 2 writes the coordinate ring map to the finite product of the refined rings. Etaleness supplies flatness through the definition, the affine flatness criterion gives flatness of each coordinate map, and the finite-product flatness node gives flatness of the product map. Joint surjectivity gives surjectivity on prime spectra by choosing a prime in one refined member over each base prime and then using the product projection; the affine-spectrum definition identifies this contraction map. The faithful-flat criterion then applies. The product ring is Noetherian componentwise, so the existing faithfully-flat Noetherian descent leaf gives the base ring Noetherian. Step 3 applies exactly the affine-open-cover definition of locally Noetherian schemes. I checked empty schemes, an empty indexing family, and the singleton identity cover; no statement or hypothesis was silently changed.

## Not duplicates

No new node was created. The existing ring node `lem-weil-pbc-faithfully-flat-descent-noetherian` is used as a cited algebraic input; it states descent for one faithfully flat ring map with Noetherian target, while this item proves the geometric etale-cover statement and constructs that ring map from the finite affine refinement.
