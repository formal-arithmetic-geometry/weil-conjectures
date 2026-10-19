# Stage-1 report: lem-coef-pattern-section-core-identification

## Files written

- dag/nodes/sec-six-functors/lem-coef-pattern-section-core-identification.json: existing statement node, now split in seven steps; not a Mathlib leaf. Its statement and maintainer metadata are unchanged.
- citations.json: thirteen verbatim statement excerpts, one for every step/node citation.
- searches.jsonl: four searches run with msearch.py, retained with their actual outcomes. The node also retains all inherited searches.

No new nodes, no new Mathlib leaves, and no unit files were written. write_split.py is sandbox-only preparation material, not part of the delivery.

## Attachments

None. Searched all of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id and section/core notions. No project declaration states this quasicategorical marked-section result. The ordinary sheaf sections hits do not concern this statement. No master sorry declaration was treated as a finished proof.

## WANTED

WANTED: an archived copy of Lurie's Higher Algebra, Lemma B.2.4(c), printed p.1484, for lem-coef-pattern-section-core-identification.
WANTED: archived Kerodon references 01F1 (exponentiation), 01DK (pointwise equivalences), and 03PM (base-change invariance), as references for the existing supporting nodes.

I read the online Higher Algebra PDF at printed pp.1483-1484, including the actual one-sentence point/interval test in B.2.4(c). The proof here is an agent-written expansion, not a claim that HA spells out the strict-fibre argument. The Kerodon web rendering did not expose the mathematical bodies to the browsing tool; I do not claim an independent reading of those bodies. I read the complete statements of the existing DAG nodes used instead. No source was downloaded or installed and no SGA source is cited.

## Problems found and corrected

The shared checkout initially lacked this recently created item, while the server's isolated project already had it. I retrieved its file by a read-only SSH cat into my sandbox. The periodic refresh has since made the same item available in the shared checkout. I retained its statement, searches, source, and ancestry. There was no earlier sandbox proof or report to overwrite.

The imported node had no proof. The important inference to justify was that equivalences in the ambient functor category have inverse witnesses in the *strict* section fibre. Steps 2 and 3 prove this directly using the vertex-determined simplices of the point and interval. I did not assume an inverse of u over B: Step 5 chooses an ordinary inverse solely to prove equivalence of the ambient functor categories, and Step 6 applies the existing isofibration base-change statement to the identity-base vertex.

The blueprint origin and unit bind this to auxiliary marked-operadic infrastructure for the mapping-complex adjunction in paragraph 2 of prop-coef-integral-exceptional-adjoint. I read that proof file and the chapter/unit records; their route is unchanged. This is not the key statement of its unit, so no realized fields require editing.

## Not duplicates

No new nodes were created. Whole-DAG searches for strict section quasicategories and whole-blueprint searches with blueprint_refs.py for 'section core', 'strict section', 'pointwise equivalences', and 'flat sharp' found no blueprint statement duplicating the item. The existing lem-coef-infinity-equivalence-section-restriction concerns precomposition along an equivalence of bases for a right fibration; this item concerns postcomposition between arbitrary inner fibrations over a point or interval and a precise marking identity. The existing lem-coef-quasicategory-full-subcategory-core-equivalence is reused for its general core-equivalence clause, rather than duplicated.

## Mathlib searches

Ran leanfinder for the section-core/marked-map identity, loogle with the exact query '"core", "SSet"', grep for section/core and marked-map expressions in AlgebraicTopology, and leansearch for categorical-equivalence invariance of strict sections. All services returned successfully. The grep returned no hits. Read every semantic and Loogle hit signature; then inspected pinned Mathlib Sections.lean:35-74, Quasicategory/Basic.lean:33-57, InnerFibration.lean:29-85 and StrictSegal.lean:50-120. The two semantic phrasings searched respectively the marking identity and the invariance clause. Ordinary-category sections, coreflective skeleton functors, and StrictSegalCore data do not state this theorem or a one-line generalization. No absent search was recorded and no compiler or Lake command was run.

## Unfinished work

None in this split. There are no new children to hand off. The supporting existing DAG nodes remain subject to their own stage-1/Lean work; this delivery does not assert that the entire transitive Lean closure is proved.

## Review by Q156

I checked the statement against HA B.2.4(c)'s intended point and interval test and against the actual constructions in the supporting node statements. The item is true as written; there is no statement dispute or added hypothesis. The following is my mathematical check against delivery-errors B through E, not an independent second reading.

Step 1 uses the full isofibration-exponentiation statement, taking the degreewise injection from the empty simplicial set into B. Its hypotheses are satisfied because E and B are quasicategories and the assumed inner fibration lifts every equivalence in B by an identity. The resulting functor map is an isofibration between quasicategories. I wrote the pullback inner-horn lifting argument explicitly rather than citing a definition as if it asserted quasicategorical pullback existence. The functor and simplicial-pullback definitions are supplied by def-cbc-enhanced-diagrams-cones. This also proves the quasicategory assertion when no sections exist.

Step 2 uses only the same definition node: simplices of Delta^0 and Delta^1 are weakly increasing vertex lists, and full subcategories contain exactly the simplices whose vertices lie in their specified set. The product map into B is therefore forced by its vertices. An inverse edge and the two witnessing triangles remain in the full section subset because their vertices are the two sections. This is an elementary calculation, not an unproved general theorem about strict fibres.

Step 3 uses the exact iff in lem-coef-infinity-pointwise-equivalences with domain B and codomain E. Step 2 lets it be applied to section edges. I separately checked that a vertical edge equivalent in E is equivalent in E_b: the inverse's endpoints and all triangle vertices lie over b, so their images in the point or interval are constant. Conversely the fibre inclusion preserves the witnesses. This is where using an arbitrary base without further work would be invalid.

Step 4 uses the coordinatewise product marking, flat marking, and sharp marking explicitly stated in lem-coef-marked-point-cartesian-model. The only marked product edges are a degenerate B edge paired with any parameter edge. Their images are exactly the components considered in Step 3. The core definition in def-cbc-enhanced-diagrams-cones then gives equality in every degree; precomposition gives the same operators. This checks the entire identity, not only its vertices or fundamental groupoids, and uses no marked model-structure theorem by implication from a definition.

Step 5 uses the quasi-inverse characterization in lem-coef-joyal-quasicategory-characterizations(2). The inverse is not assumed over B. The evaluation formula defines the transformations on functor simplicial sets, and the exact pointwise-equivalence iff is applied twice to see that these transformations are natural equivalences. All internal functor categories involved are quasicategories, as follows by exponentiation of their terminal isofibrations. The equation qu=p, not a property of the chosen inverse, proves the required commutation over Fun(B,B).

Step 6 checks every hypothesis of lem-coef-infinity-isofibration-base-change: the common base is the quasicategory Fun(B,B), both projections are the isofibrations from Step 1, u_* is the functor equivalence of Step 5, its base equation is strict, and the base-change domain is Delta^0 at id_B. Its conclusion supplies the section equivalence. The Joyal characterization changes the functor-equivalence wording to categorical-equivalence wording. I read the *general final clause* of lem-coef-quasicategory-full-subcategory-core-equivalence: it explicitly gives a weak homotopy equivalence on cores for every coherent functor equivalence, and permits emptiness. I did not use its narrower replete-subcategory clause on the non-replete set of strict sections.

Step 7 checks naturality on the actual family maps and inverse witnesses. Pullback and postcomposition preserve the marking conditions. I tested B=Delta^0, the identity fibration, an empty total space, an empty vertex fibre over the interval, and a discrete two-point E mapping bijectively on vertices to the interval: the latter has both vertex fibres nonempty but no sections. The identity and the base-change argument still give exactly the claimed empty simplicial sets. No surjectivity or nonemptiness premise is hidden in the proof.

I compared each citation to its node's statement and copied a verbatim excerpt into citations.json. All statements used as theorems are cited, all elementary steps have their short arguments written out, and no source tag substitutes for a node. No new elementary, duplicate, or clause-restating nodes were introduced (B, C1/C4, D1/D2). The only non-elementary tools are existing nodes in the item's unit. Every step is under 1000 characters, so no step crosses the 2000-character hidden-lemma review threshold. Hypotheses, objects, the fibre ring/category distinction, inverse witnesses and naturality have been checked as above (E1-E6). Nothing was weakened to make it provable.
