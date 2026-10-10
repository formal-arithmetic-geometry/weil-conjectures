Files written:

- `dag/nodes/sec-smooth-base-change/def-sbc-normal-dominant-galois.json` — definition, no new nodes, Mathlib searches found no exact match.
- `citations.json` — empty because the item is a definition with no proof steps.

Attachments: none.

WANTED: none.

The item is a blueprint definition, not a theorem. I checked the item source recorded in the node and the unit/chapter context. The existing dependency `def-weil-pbc-scheme-conventions` supplies the ambient scheme conventions; the item introduces the combined terminology for integral and normal schemes, dominant morphisms, finite etale Galois covers, and geometrically connected or reduced fibres. No existing DAG node states this combined definition, and no separate primitive node is needed: these are the clauses of the definition itself. I searched the Lean source for the blueprint tag and relevant terminology; it contains only references and explanatory comments, with no declaration for this definition. The required LeanFinder, Loogle, grep, and LeanSearch searches were run; LeanSearch was unavailable and recorded as such. I checked that no proof dependencies or citations are required for a definition, and set the item status to `split` with `blueprint.same_as = []`.

## Review by H1

I read the item JSON, its recorded blueprint source and the `sk-def-smooth` unit context. The statement is unchanged. Its only statement dependency remains `def-weil-pbc-scheme-conventions`, which is the ambient scheme convention explicitly used by the definition. I inspected all source hits for `def-sbc-normal-dominant-galois` and for normal, dominant, Galois, and geometrically connected terminology in the project Lean source; none states the full definition. Since there are no proof steps, there are no cited-node quotes and `citations.json` is empty. I also checked the DAG and blueprint search for an equivalent node and found none. The Mathlib searches returned only unrelated general declarations or no hits, so no Mathlib leaf or extra node was created.

What could not be finished: nothing; this is a definition-only split.

## Second reading by H1

- Item statement: checked against blueprint node `def-sbc-normal-dominant-galois`, order 1379, and the scheme/morphism convention nodes; repaired the missing explicit convention citation and the geometric-reducedness quantifier.
- New nodes: none; the item remains a definition-only split, so B1, proof-step dependencies, and citation quotes are vacuous.
- Small cases: integral and normal definitions behave correctly for the empty/zero scheme and fields; dominance is the dense-image condition; a finite etale torsor over a field has the stated fibrewise action; geometric connectedness is stable under field extension, while geometric reducedness requires all field extensions over imperfect fields.
- Existing-node and Mathlib checks: searched the repository for the combined definition and for Galois/torsor/geometric-fibre declarations; no duplicate or exact Mathlib definition exists. The recorded searches remain unchanged and accurately report LeanSearch unavailability.

Changes made: removed the non-self-contained reference to a "deck-group lemma below," made the existing scheme and morphism convention dependencies explicit, changed geometric connectedness/reducedness to quantify over every field extension, and retained `blueprint.same_as` as the required empty list. These repairs preserve the intended definitions while making the node self-contained and correct over imperfect fields.
