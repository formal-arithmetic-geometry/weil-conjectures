# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-fppf-local-qf-neighbourhood.json` — item, statement node, no new Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node and proof step.

Attachments:

- No finished Lean declaration was found for the item. The existing declaration for the CM-slice node is an attachment to that existing node, not to this item.

WANTED:

- None.

What was checked and corrected:

- The imported item statement agrees with Stacks Project, `more-morphisms.tex`, Tag 0571: flat and locally finitely presented, with an image point, produces a factor through a flat locally finitely presented locally quasi-finite morphism meeting that point. No hypothesis or conclusion was changed.
- The item was not already proved in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the keyword and blueprint-tag searches found no declaration. The existing parent `lem-trf-fppf-local-qf-refinement` cites this item and remains unchanged.
- The whole DAG and blueprint were searched for Tag 0571 and for the neighbourhood statement. No duplicate node exists. The proof uses existing nodes `lem-trf-flat-lfp-cm-locus-fibre-dense`, `lem-sbc-fibre-cohen-macaulay-locus-open`, `lem-sc-lft-over-field-jacobson-space`, and `lem-trf-cm-closed-point-flat-quasifinite-slice`; each was opened and its statement checked against the step where it is cited.
- Mathlib searches for the item were run with `msearch.py`: LeanFinder found only generic flatness/open-map and finite-presentation declarations, Loogle returned no hit, grep found no quasi-finite-neighbourhood theorem, and LeanSearch found only definitions/instances. These are recorded in `searches.jsonl`; no Mathlib declaration states the item.

## Review by NZ

I read the Tag 0571 statement and proof at `literature/stacks-project/more-morphisms.tex` and checked the item statement clause by clause. Step 1 handles the nonempty fibre from the image-point hypothesis. It uses the existing density statement `lem-trf-flat-lfp-cm-locus-fibre-dense` and the openness statement `lem-sbc-fibre-cohen-macaulay-locus-open`; their statements provide exactly the Cohen–Macaulay points and the open ambient locus used here. The fibre is locally of finite type over the residue field by the item's locally finite-presentation hypothesis, so `lem-sc-lft-over-field-jacobson-space` supplies a closed point in the nonempty open intersection. On an affine finite-type chart over the field, the fibre stalk is Noetherian, so the selected point satisfies every hypothesis of the CM-slice node. The affine-fibre and local-finite-presentation references are used only for these elementary fibre and stalk observations.

Step 2 applies `lem-trf-cm-closed-point-flat-quasifinite-slice` exactly with the chosen closed point. I checked that its statement supplies a scheme, map to the original source, a point over the selected fibre point, and a composite that is flat, locally of finite presentation, and locally quasi-finite. Step 3 is the elementary composition check: the slice point maps to the selected point over `s`, hence `s` lies in the image of the composite, and the composite equality is the required `g=f∘h`.

I tested the edge cases of an empty source (the image-point hypothesis then cannot hold), a one-point identity morphism, and a zero-dimensional affine fibre. The searches, proof dependencies, and citation quotes were updated together; no new node was created and no statement was weakened.

What could not be finished: nothing.
