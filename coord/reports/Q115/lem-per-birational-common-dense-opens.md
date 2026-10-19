# Delivery report: lem-per-birational-common-dense-opens

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-birational-common-dense-opens.json` — split statement, no new Mathlib leaf.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-birational-generic-localization.json` — one new unsplit algebra statement; Mathlib searches found no exact match.
- `citations.json` — verbatim statement quotes for every proof-step citation.

Attachments: none.

WANTED: none.

The item is sourced from the Stacks Project, Tag 0BAC (`morphisms-lemma-birational-birational`), locally-of-finite-presentation alternative (2). I read the complete proof in `literature/stacks-project/morphisms.tex`: its affine reduction, the generic-fibre localization lemma (Tag 0BAB), denominator clearing, finite-presentation kernel argument, and principal-open conclusion. The new child node records only the intermediate ring claim used there, namely that the localization at the base minimal prime agrees with the generic local ring when the generic local rings are isomorphic. It is strictly smaller than the item and is not a restatement of the common-open conclusion.

## Review by Q115

I checked the item statement against Tag 0BAC and retained all of its hypotheses, including local finite presentation, finite numbers of irreducible components, bijection on generic points, and the stalk isomorphisms. I checked the edge cases of one component, a nilpotent thickening, and an isomorphism: the proof uses no reducedness or separatedness and the principal open still contains every relevant generic point.

Step 1 is the source's initial reduction to irreducible affine charts. I read the statements of `lem-weil-pbc-affine-opens-basis`, `lem-sc-scheme-sober`, and `lem-weil-pbc-spec-irreducible-components-minimal-primes`; together they provide affine neighbourhoods and identify the generic points with the minimal primes used in the chart calculation. Step 2 uses `lem-weil-pbc-spec-map-stalk-localization` for the stalk/localization identification and the new `lem-per-birational-generic-localization` for the equality of the two localizations. I verified that the child assumes unique minimal primes and the contraction relation, exactly what the generic-point bijection supplies after Step 1.

Step 3 follows the finite-presentation paragraph of Tag 0BAC. I read `lem-weil-pbc-lfp-affine-opens-finite-presentation`, which states that the affine chart ring map is finitely presented, and `lem-weil-pbc-finite-presentation-surjection-kernel-fg`, which states that a polynomial surjection onto a finitely presented algebra has finitely generated kernel. The denominator clearing and finite list of kernel generators are then explicit localization calculations. Step 4 uses `lem-weil-pbc-principal-localization-open-immersion` and the definition node `def-weil-open-immersion` to turn the localized ring isomorphism into an isomorphism of principal open subschemes; the choice outside the generic prime makes the opens dense. Step 5 records the finite-component undoing of the reduction and uses only the irreducible-component notion.

I searched the whole DAG and blueprint before adding the child. No existing node states its generic-localization claim, and no node carries Tag 0BAB. The item has no duplicate child and no Mathlib match. The required Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`; the semantic searches returned only general localization/ birational declarations, while the grep and Loogle results did not state the child. The server `check_dag` preflight passed before this report was written.
