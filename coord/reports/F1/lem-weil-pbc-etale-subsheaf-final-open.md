Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-subsheaf-final-open.json`: statement split into three proof steps; no new node.
- `citations.json`: verbatim citations for all step dependencies.
- `report.md`: this worker report.

Attachments: none.

WANTED: literature/stacks-project/etale-cohomology.tex, Lemma Tag 04HV, if the fetched source corpus is restored; the imported node identifies this source and place.

The item was unsplit despite having an imported statement. The existing node `lem-weil-pbc-etale-sections-equal-open` invokes this item, so citing that node here would create a cycle. I therefore followed Tag 04HV directly and used only the existing openness lemma for the non-elementary geometric input. No statement change was made.

## Review by F1

I read the item's imported statement and the neighboring Tag 09XM split. The source route is Tag 04HV: construct the open as the union of images of etale objects carrying a section, glue local sections using the sheaf equalizer condition, then prove uniqueness and identify the stalk criterion. Step 1 uses the definition of a sheaf of sets for the subsingleton behavior and `lem-weil-pbc-etale-morphism-open-map` for openness of each image. Step 2 uses the same sheaf equalizer statement to glue pulled-back singleton sections on an etale cover; the openness lemma supplies the local images used in the construction. Step 3 uses the geometric-stalk definition to turn a pointed neighborhood section into a stalk element, and the geometric-point definition for the point under discussion; subsingleton follows from the final-sheaf inclusion.

I checked the hypotheses: every object used in the union is etale over the given scheme, every local section is in the subsheaf, and overlap restrictions agree because the ambient final sheaf has one section. The uniqueness argument tests both candidate opens by their open immersions. Small cases checked mentally were $H=\varnothing$, giving $W=\varnothing$, and $H$ equal to the final sheaf, giving $W=S$; the stalk criterion agrees in both cases. The Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such in the search log, while the other three found no direct declaration.

## Second reading by F1

- Source Tag 04HV (`lemma-support-subsheaf-final`) was read in the fetched Stacks `etale-cohomology.tex`; the item's hypotheses and conclusion are the representability statement expanded from $H=h_W$, with the factorization and stalk formulations, and agree hypothesis by hypothesis.
- Step 1 was checked against the definition of a subsheaf of the final sheaf (subsingleton sections), the sheaf equalizer definition, and `lem-weil-pbc-etale-morphism-open-map`; the union construction and openness are correct.
- Step 2 was checked against the sheaf equalizer statement and the etale-openness statement; base change gives an etale cover over the factorization open, and singleton sections glue uniquely. The empty and final sheaf cases were checked.
- Step 3 was checked against the open-immersion uniqueness test, `def-weil-pbc-geometric-stalks`, and `def-weil-geometric-point`; the stalk criterion is exactly the pointed-neighborhood colimit criterion and subsingleton makes nonempty equivalent to singleton.
- There are no new nodes in this split; consequently B1--B7 and duplicate-search checks have no new-node findings. Existing cited nodes were opened and their quoted statements in `citations.json` are verbatim.
- The Mathlib search records were checked against `searches.jsonl`; no direct declaration was found. The dry run `deliver.py F1 lem-weil-pbc-etale-subsheaf-final-open --no-push` passed preflight.

Changes made: none to the item, proof, or citations; appended this second-reading audit only. The source corpus was absent from the repository, so Tag 04HV was fetched to `/tmp` for the source comparison and was not added to the delivery.
