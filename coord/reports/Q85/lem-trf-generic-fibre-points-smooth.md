# Stage-1 report: lem-trf-generic-fibre-points-smooth

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-points-smooth.json` — statement, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-smooth-at-point-fibre-criterion.json` — statement-only auxiliary lemma; Mathlib searches found no match.
- `citations.json` — verbatim citations for every non-elementary step.

## Attachments

None. No sorry-free project declaration states the item exactly.

## WANTED

None. The cited Stacks Project files are present in `literature/stacks-project/`.

## What was wrong or incomplete

The imported item had an empty proof and was therefore unsplit. The DAG already contained the Tag 056V dense smooth-locus statement, but it lacked the scheme-level pointwise form of Tag 01V9 needed to pass from smoothness of the fibre at one point to smoothness of the original morphism at that point. I added that exact general criterion as an unsplit statement-only node. The item statement itself is unchanged.

## What could not be finished

The auxiliary criterion remains a statement-only node, as required for a one-level stage-1 split; it is sourced directly to Stacks Tag 01V9 and is queued for a later split or attachment review.

## Review by Q85

I read the imported item and its source citation (Stacks `varieties.tex`, Tag 056V, together with `morphisms.tex`, Tag 01V9), and I read the full statements of both cited DAG nodes. Step 1 uses `lem-pur-geometrically-reduced-dense-smooth-open`; its statement explicitly gives a dense smooth locus for a locally finitely presented geometrically reduced scheme over a field. I checked that the geometric-fibre reducedness hypothesis is exactly geometric reducedness of the fibre over `κ(s)`, and that finite presentation survives the fibre base change. Step 2 is elementary topology: a dense open meets every irreducible component densely, hence contains that component's generic point. Step 3 uses the new `lem-trf-smooth-at-point-fibre-criterion`, whose statement is precisely Tag 01V9 (1)⇔(2); the item's flatness hypothesis supplies the required flat local ring map and its finite-presentation hypothesis supplies local finite presentation. I checked the conclusion's open-neighbourhood wording against the item's smooth-at-a-point convention. I tested the edge cases of a field base, a one-point reduced fibre, a reducible fibre with several components, and an empty scheme (the quantified conclusion is vacuous in the last case). Mathlib searches for the item and auxiliary criterion were run with LeanFinder/LeanSearch/Loogle/grep and found no exact Mathlib theorem. The citation quotes are verbatim substrings of the cited node statements. No statement was weakened, no duplicate auxiliary node was found, and no SGA source was used.

## Not duplicates

- `lem-trf-smooth-at-point-fibre-criterion` vs `lem-trf-generic-fibre-points-smooth`: the auxiliary node is the general pointwise equivalence for any locally finitely presented morphism with a flat local map; the item adds flat finitely presented Noetherian hypotheses, geometrically reduced fibres, and the generic-point conclusion.
- `lem-trf-smooth-at-point-fibre-criterion` vs `sk-thm-geo-generic-open`: the auxiliary node states Tag 01V9 (1)⇔(2) for one point; the existing theorem concerns generic constructibility and universal base change for direct images and only cites 01V9 inside its proof.
- `lem-trf-smooth-at-point-fibre-criterion` vs `sbc-lem-smooth-criterion`: the auxiliary node is pointwise and assumes flatness only at one stalk; the existing node is the global equivalence requiring every fibre to be smooth.
- `lem-trf-smooth-at-point-fibre-criterion` vs `lem-trf-smooth-at-point-differential-criterion`: both are pointwise Tag 01V9 inputs, but the auxiliary node uses smoothness of the fibre at the point, while the existing node uses the bound on generators of the relative differential module.
