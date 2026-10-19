## Files written

- `lem-weil-point-sections-tensor-shift.json`: existing item, repaired and split; no new nodes.
- `citations.json`: verbatim statement citations for all three proof steps.
- `report.md`: this report.

## Attachments

None. I searched the project source for the item id and its relevant sections-tensor names; no sorry-free declaration states this item exactly.

## WANTED

None.

## Corrections and source checks

The imported item listed `lem-weil-point-sections-exact`, but that id does not exist in the DAG. The exact existing node is `lem-weil-point-proetale-sections-exact`; I corrected the item dependency to that id. The mathematical statement and its coefficient hypotheses were otherwise retained. The item is a supporting lemma for the final display of `def-weil-finite-coefficient-point`; the blueprint has no separate node for this shift assertion, so no new node was created.

I read the blueprint definition `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-weil-finite-coefficient-point.md`, the Stacks section-tensor source named in the item, and the existing statements of `lem-weil-point-sections-scalar-extension`, `lem-weil-point-proetale-sections-exact`, `lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`, and `def-pur-sheaf-tensor-product`. The proof follows the source’s final-display route: choose a K-flat model, write the sections-tensor map degreewise, check its shifted components including the common differential sign, and descend through the canonical resolution-independent derived comparison.

## Review by NX

I checked the item statement against the final-display argument in `def-weil-finite-coefficient-point`: the global finite-field datum, finite extension `E ⊂ L`, completed coefficient sheaves, constructible derived-complete input, exact final-object sections, and the ordinary-versus-derived tensor distinction all agree with the imported statement. The dependency correction was made because the cited exact-sections node is named `lem-weil-point-proetale-sections-exact` in the DAG.

Step 1 uses `lem-pc-kflat-resolution` for a K-flat resolution with flat terms, `lem-pur-derived-change-of-rings` for the derived tensor represented by the ordinary tensor on that model, and `lem-weil-point-sections-scalar-extension` for the canonical sections-tensor map. `def-pur-sheaf-tensor-product` supplies the sectionwise presheaf tensor and sheafification, so the displayed balanced formula is the actual map. Step 2 uses the exact-sections statement’s explicit commutation with shifts and checks the degree reindexing and common shift sign directly; the degree-zero coefficient section introduces no extra sign. Step 3 uses the exact-sections preservation of quasi-isomorphisms and the canonical comparison between any two K-flat resolutions from `lem-pur-derived-change-of-rings`, together with naturality of the scalar-extension comparison, to justify descent from chain maps to roofs and independence of the chosen resolution.

I tested the shift calculation on `m=0`, `m=1`, and a successive pair of shifts: the component is the same tensor formula at the reindexed degree, and the differential signs occur on both sides. The zero complex and zero coefficient section give the zero map. No new node was needed because every non-elementary input is already represented by an existing DAG statement. The Mathlib searches found only generic additive-functor and homological-complex shift declarations, with no theorem for this specified pro-etale sections-tensor comparison; those searches are recorded in the item and `searches.jsonl`.
