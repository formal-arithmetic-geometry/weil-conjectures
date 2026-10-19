# Stage-1 report: lem-trf-open-relative-normalization-gluing

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-open-relative-normalization-gluing.json`: item split into four proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None.

## WANTED:

None.

## Not duplicates

No new node was created, so there are no duplicate pairs to resolve. The proof reuses `lem-weil-pbc-integral-closure-commutes-localization` and `lem-weil-pbc-glue-schemes` after reading their statements.

## Review by Q74

I read the imported item, its parent `lem-trf-integral-surjective-open-extension`, the unit `sk-i-curve-zero`, and the source passages in `literature/stacks-project/more-morphisms.tex` (Tag 0CNX and the normalization construction), `literature/stacks-project/morphisms.tex` (Tags 0307 and 035K), and `literature/stacks-project/schemes.tex` (Tags 01JA–01JC). I also read the existing DAG statements for the integral morphism, affine spectrum, integral closure, module localization, integral-closure localization, fibre product, and scheme gluing nodes.

Step 1 uses only the definitions of an integral morphism, affine spectrum, and integral closure; I verified that the map from `A` to `B_i` is the composite through `A_{f_i}`. Step 2 uses exactly the existing localization theorem: its statement identifies the localization of the integral closure with the integral closure after localization. Together with integrality of `A_{f_i}→B_i`, this gives the chart restriction and the cocycle by transitivity of localization. Step 3 uses the existing scheme-gluing statement for open charts and the definitions of integral morphism and fibre product. Step 4 uses the same localization and gluing statements to compare constructions on intersecting affine opens; integrality is checked on the affine target cover, and the localized charts recover `V` over `U`.

I checked the edge case where `W∩U` is empty: the principal cover is empty and the affine-local construction contributes no chart over that open, while the global affine-cover gluing is carried out on opens meeting `U`; this is consistent with the standard Tag 0CNX extension construction. I retained the statement's “integral closure of A in B_i” wording and made the intermediate `A→A_{f_i}→B_i` map explicit, since localization then recovers the closure over `A_{f_i}`. The required Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`; they found generic normalization and gluing APIs but no exact arbitrary-open extension theorem, so the item remains a document-sourced statement rather than a Mathlib leaf.
