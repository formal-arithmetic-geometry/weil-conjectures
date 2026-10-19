# Q74 stage-1 report: lem-coef-enriched-completion-localization

## Files written

- `dag/nodes/sec-six-functors/lem-coef-enriched-completion-localization.json`: repaired item, status `split`.
- `dag/nodes/sec-six-functors/lem-coef-simplicial-model-arrow-lifting.json`: new statement-only supporting node, Mathlib search verdict no match.
- `citations.json`: verbatim statement quotes for every proof-step citation.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item or the new supporting node. The source grep for the item tag and its enriched categorical terminology found no attachment.

## WANTED

WANTED: David Gepner and Rune Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, arXiv:1312.3178v4, Theorem 5.3.17 and the proof paragraphs through Proposition 5.3.16, for the item and the new arrow-representation node. The HTML source was read online, but the paper is not archived under `literature/`.

## Not duplicates

- `lem-coef-simplicial-model-arrow-lifting` vs `lem-coef-simplicial-presheaf-localization-comparison`: the existing node identifies the localization of simplicial presheaves for a fixed ordinary indexing category; the new node concerns essential surjectivity on arrow categories after an arbitrary pullback over the infinity category of spaces.
- `lem-coef-simplicial-model-arrow-lifting` vs `lem-coef-cosimplicial-frame-mapping`: the existing node states mapping-space models and actual-map representatives inside one model category; the new node packages the endpoint replacement and coherent pullback arrow needed for an arbitrary functor over spaces.
- `lem-coef-simplicial-model-arrow-lifting` vs `lem-coef-localization-cartesian-pullback`: the existing node is a localization theorem for a Cartesian fibration; the new node has no Cartesian-fibration hypothesis and only supplies arrow representatives in the simplicial-set pullback.

## What was repaired

The item was already a complete seven-step split in the shared material, with the statement and route matching Gepner–Haugseng Theorem 5.3.17. The dedicated return for Q74 required re-splitting former step 6 because its 2309-character non-elementary argument hid the Kan-model replacement and homotopy-pullback lifting lemma. I created `lem-coef-simplicial-model-arrow-lifting` as a statement-only node and replaced step 6 by a 1133-character argument citing that node. The item statement, hypotheses, conclusion, other six steps, blueprint ancestry, and inherited searches were retained.

I read the full statements of every node cited by each step. In particular, step 6 now takes only the new node's explicit conclusion (an FFES arrow has an equivalent representative over an actual simplicial map), then uses the existing definition of FFES and the localization universal property. Steps 1, 2, 3, 4, 5 and 7 continue to cite the existing algebroid fibration, simplicial-presheaf localization, pointwise-adjoint, Cartesian-pullback, frame, Kan–Quillen, and enrichment-change nodes; their hypotheses remain explicit. `proof_deps` was regenerated as the union of step uses, and every pair has an exact full-statement quote in `citations.json`.

For the new node I checked the source statement against the last localization comparison in Theorem 5.3.17: choose Kan representatives for both object spaces, represent the base mapping-space component by an actual simplicial map using the model localization, and use the homotopy-pullback mapping-space formula to lift the enriched arrow. The empty Kan complex and identity/terminal cases are included. The statement is strictly supporting and does not restate the item's localization equivalence.

I searched the whole DAG and blueprint before creating the node, including the existing simplicial model, localization, arrow-fiber, and Kan mapping results. The required `msearch.py` searches were run and logged in `searches.jsonl`: LeanFinder and LeanSearch returned only ordinary Mathlib arrow/model-category results; Loogle returned no hits; grep returned ordinary localization and hom-constructor declarations. I read the relevant Mathlib files and recorded the verdict as no match. No Mathlib leaf was created.

## Review by Q74

I reread `AGENTS.md`, `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E. I opened the item and every existing dependency in the shared DAG, then compared the item to Gepner–Haugseng Theorem 5.3.17 and its displayed simplicial-set pullback construction. The monoidal infinity-category hypothesis, variable versus discrete object spaces, FFES class on both sides, coherent localization, and naturality clause are all retained exactly.

For step 1, the object-space Cartesian fibration node supplies the projection, its mapping-space fibre formula, and the equivalence/object criterion; the simplicial-presheaf comparison supplies passage from simplicial sets to spaces. For step 2, the same fibration node supplies the restriction mapping formula, while the pointwise-adjoint criterion supplies assembly of the right adjoint. For step 3, the fibration node supplies Cartesian/full-faithful equivalence, vertex coverage, and restriction of FFES; the step is elementary from those statements. Step 4 is the short unit/counit localization argument and is elementary. Step 5 uses the localization-Cartesian-pullback statement and the simplicial-presheaf and fibration nodes; all localization hypotheses are present and the inclusion of equivalences into FFES is stated. Step 6 now cites only `lem-coef-simplicial-model-arrow-lifting`; that node states the exact endpoint Kan replacement, actual simplicial map, homotopy-pullback lift, and equivalence to the original arrow used here. Step 7 uses the fibration node's postcomposition/change-of-enrichment clause to obtain coherent naturality.

I checked every cited statement rather than relying on a node's proof. The new node introduces all objects and universes itself, has no proof sketch, uses the correct online source place, and has all three required Mathlib search kinds recorded. I tested the new statement on an empty object space, a terminal space, a discrete two-point space, and an identity arrow; no edge case adds a hidden nonemptiness or Cartesian hypothesis. The new node has no cycle back to the item. All proof steps are below the 2000-character long-step threshold after the repair, and the new node is statement-only as required.

No source error or statement dispute was found. No Lean, compiler, Lake, or build tool was run, and no live repository file was changed.
