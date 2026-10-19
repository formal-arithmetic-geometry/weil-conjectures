# Q147: lem-per-dominant-part-coreflection

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-dominant-part-coreflection.json`: statement, split in eight proof steps. Mathlib verdict: no match. No new nodes; no new Mathlib leaves.
- `citations.json`: 27 citations, each quoting the actual cited node statement verbatim.
- `report.md`: this report. `searches.jsonl` records the four actual msearch invocations; `write_split.py` is sandbox-only drafting scratch.

## Attachments

None. Searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag, coreflection, maximally dominant schemes, dominant components, dominant part, and generic closures. The hits concern unrelated coreflections, generic-point topology and generic finiteness. No project declaration states all the clauses of this item. The item has no pre-existing Lean audit requiring an open-declaration attachment.

## Literature wanted

None. The ILO PDF and the cited Stacks sources are available locally.

## Errors and changes

The original mathematical statement is correct. Its clauses were originally unsupported by any proof steps. I retained the statement and its source, added the generic-point and scheme-fibre definition dependencies, and supplied the proof. The generic-fibre statement does not require a reduced base: the existing Stacks 054Z node has exactly the generality needed. The etale comparison is stronger than the open-immersion assertion explicitly written in ILO II 1.2.8; it follows by the same open-map closure argument together with reduced etale pullback, and is proved rather than attributed verbatim to ILO.

The blueprint ancestor is `lem-per-artin-gabber-affine-curve`; the item enters through its Step 3 finiteness/duality input and the existing alteration-cover calculus. Read the chapter and `sk-p-dl-a1-perverse` unit records. This item is not the unit's statement node, so no unit realization file was changed. Blueprint searches for dominant, generic point, irreducible, reduced, etale, and base change found no imported node duplicating this item; the individual tools already exist and were reused. No new nodes were created, so there are no same-tag new/existing pairs to distinguish.

The Mathlib search log has two different semantic phrasings, Loogle on IsDominant/IsReduced, and a grep of AlgebraicGeometry for maximally dominant/generic closure vocabulary. Read all returned types. The ideal-sheaf kernel adjunction is an adjunction of ideal data and closed subschemes, not the asserted coreflection over S. Reducedness, dominance, rational-map and geometric-reducedness hits do not state the item or imply it by a one-line specialization. The old searches in the item were preserved and the four new searches were appended with their actual result lists/counts.

## Not finished

No mathematical part remains unfinished. Stage 1 only: no Lean was written and no compiler, Lake, or build tool was run. Delivery validation is recorded below after the required server dry run.

## Review by Q147

I read ILO, Expose II 1.1.1--1.1.5 and 1.2.5--1.2.8, printed pp. 23--26, directly from the PDF. Section 1.2.5 gives the reduced dominant union and coreflection; the proof of 1.2.6 uses its reduced generic-fibre formula; 1.2.8 proves properness and surjectivity by the closed image containing the generic fibres. I compared every proof citation with the statement of its current DAG file, not with that file's proof. There are no new-node sources to audit.

Step 1 uses `def-pc-scheme-fibre` for the homeomorphism onto the inverse image of the point, `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-noetherian-finitely-many-components` for the finite component list, and `lem-sc-irreducible-components-cover` with `lem-sc-scheme-sober` for a component generic point generalizing every point. Those statements explicitly provide these facts. I checked Stacks 01T6 and 01IS in morphisms.tex/schemes.tex. The only extra topology is written out: a component generic point has no strict generalization, and continuity preserves specialization. This gives both containments between the generic-fibre closure and the finite union of dominant components.

Step 2 uses the existence, reducedness, support and uniqueness clauses of `lem-weil-pbc-reduced-induced-closed-subscheme` (Stacks 01J3/01J4). `lem-weil-pbc-closed-immersion-proper` explicitly makes a closed immersion proper, hence finite type, and `lem-sfb-finite-type-composition-base-change` explicitly composes finite-type maps. The generic points of the selected components map into G by their selection. The finite-union component argument is elementary and included in the step, not made into another node.

Step 3 again uses component coverage and sobriety. Their generic points lie above G by the hypothesis on T; continuity puts every image point in the closed support C_X. `lem-weil-pbc-reduced-source-factors-through-closed-subscheme` states exactly that reduced sources with set-theoretic image in a closed subscheme factor through it; I read Stacks 0356 and checked reducedness of T at this use. I did not apply a false factorization criterion to an arbitrary nonreduced source. Uniqueness is justified using the surjective-ring-map description in `def-weil-closed-immersion`. Step 4 then needs no additional theorem: it checks identity, composition and both naturalities by this unique factorization.

Step 5 uses the closed-immersion base-change clause (b) of `lem-weil-pbc-proper-fp-permanence`, and the fibre-topology clause of `def-pc-scheme-fibre`. All points of X_s lie in C_X, so the resulting closed immersion has full support. `lem-pur-reduction-generic-fibre` explicitly allows an arbitrary base scheme and a generic point of any component; applied to the already reduced X_md it makes its fibre reduced. I read Stacks 054Z in more-morphisms.tex, including its reduction of the affine algebra to a localization. The full-support uniqueness in the reduced-induced node and the definition of reduction finish the canonical identification. I did not assume that arbitrary fibres of reduced schemes are reduced.

Step 6 uses precisely the flat and locally finitely presented conditions in `def-weil-etale-morphism` and the open-map conclusion of `lem-weil-pbc-flat-lfp-open`. Both directions of the closure identity are included, with the reverse direction proved using an arbitrary neighbourhood, its open image, and a point over that image. No unrecorded flat-generization or component-correspondence theorem is hidden here.

Step 7 uses `lem-weil-pbc-etale-scheme-base-change` (02GO) for the projection P to Y_md, `etale-proposition-etale-reduced` for reducedness, and again the closed-immersion base-change clause and the full uniqueness clause of the reduced-induced node. I read the source 02GO in morphisms.tex and the cited 025O local-ring proposition in etale.tex; the latter's Noetherian local setting suffices here, since X and Y_md are Noetherian and P is a closed subscheme of X. The DAG node states the true general reducedness implication. The support is C_X by Step 6, and uniqueness identifies the particular comparison morphism furnished by the fibre-product universal property, not an unspecified isomorphism.

Step 8 uses the explicit composite-proper clause of `lem-weil-pbc-closed-immersion-proper`, then `lem-weil-pbc-proper-to-separated` for the map into Y_md, which is separated over Y because its inclusion is proper. `def-weil-proper-morphism` provides closedness of the image; `lem-weil-pbc-surjective-base-change` provides surjectivity on each generic fibre. Their conclusions match the use in the step. Density and closedness are then applied to the actual underlying space C_Y, not to all of Y if Y has vertical components.

I tested empty S/X/T, a scheme supported entirely in a closed nongeneric fibre (dominant part empty), several base components and their intersections, and a nonreduced one-point base Spec(k[e]/(e^2)) (dominant part is X_red). For the etale clause the identity and empty etale maps agree with the construction. The proper-surjection argument still works when the dominant part is empty, and uses closedness essentially. Each non-elementary step is below 2000 characters; none conceals a separate comparison lemma. All non-elementary input is already a cited node. Off-unit generic tools are declared in `split_report.tool_uses`; they support the original ILO route rather than replace a unit step. I checked B1--B10, C1--C8, D1--D5, and E1--E7: self-contained statements, exact citations, actual searches, no new duplicate/clause nodes, correct hypotheses and objects, complete arguments, and preserved blueprint provenance.
