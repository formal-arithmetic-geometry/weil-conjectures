# Stage-1 report: lem-trf-multisection-component-overlap-neighbourhood

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-multisection-component-overlap-neighbourhood.json`: existing statement split in five steps, unchanged statement and statement dependencies. No new nodes and no new Mathlib leaves.
- `citations.json`: 12 entries, one per step/node citation, with verbatim statement substrings.
- `searches.jsonl`: actual logged searches made by msearch.py; the existing item's historical searches were preserved and the five new records appended to mathlib_searches.
- `report.md`: this report.

## Attachments

None for the item. Searched the whole project source under lean/WeilConjectures for the exact blueprint id and for section-component, multisection and overlap terminology. No declaration states all clauses of this item. The existing theorem AlgebraicGeometry.section_component_preimage_of_isPullback in AlgebraicGeometry/SectionComponentPullback.lean gives the generic cartesian comparison only; it is already attached to lem-sbc-section-component-cartesian, which this split cites rather than duplicating. Its source was read.

## Literature wanted

WANTED: none.

## Findings and corrections

The statement is true and was retained verbatim, including the absence of any finiteness, flatness, nonemptiness or surjectivity hypothesis on p. The original proof was empty. The source is Stacks Tag 057I, more-morphisms.tex, lemma-descent-connected-fibres, from the construction of X_Z through the equality over W, supported by Tags 055M and 055R. This subargument does not require the source lemma's finite locally free multisection hypothesis: it is only needed later, when shrinking the original base using the closed map q. We stop before that step. The source lists the overlap fibre as a finite set, but W is directly the intersection of two inverse images of opens, so its construction also works for an infinite fibre.

The source's displayed projection to Z times_W Z after constructing W has an apparent typographical error: the projection is X times_Y (Z times_Y Z) to Z times_Y Z. The item's h already has the correct target. No statement dispute or correction of the item was needed.

The newest blueprint under literature/blueprint/latest was read for lem-trf-local-term-locality and its proof. This ancestor is a contracting-local-term statement; it has no separately stated multisection overlap lemma. The present item is a generic tool much farther down its recorded alteration/flatification chain. We retain that ancestry and the unit route; the chapter and unit records are unchanged.

## Not duplicates

No new node was created. The existing nodes lem-trf-flat-reduced-section-component-open and lem-sbc-section-component-cartesian already supply the substantial openness and base-change inputs. The existing Mathlib leaves lem-weil-pbc-flat-morphism-base-change and lem-weil-pbc-qcqs-morphism-permanence supply preservation of flatness and finite presentation. In particular the similarly named lem-weil-pbc-finite-presentation-base-change-composition is a ring statement, so we use the scheme permanence node, rather than claiming the ring statement alone proves scheme base-change preservation. Blueprint searches for connected component, multisection and connected-along-section, and the whole-DAG searches for Tags 055M, 055R and 057I and section/component terminology, found no equivalent blueprint statement to record in same_as.

## Mathlib searches

All five new queries were run through the required NP/item msearch.py command and their actual responses read. Loogle returned no result for the GeometricallyConnected/connectedComponent pair. The logged grep found an unrelated order-connected-section formula. LeanSearch gave topological quotient/component results and sheaf-section extensionality, not the relative scheme assertion. The first LeanFinder query gave flat-generalizing and structure-sheaf spreading results, also not a match. A second, more topological phrasing gave connectedComponent_eq, connectedComponentIn_eq and connectedComponent_eq_iff_mem. These prove the elementary component equality used in step 5, not the item's openness or cartesian comparison. No part is misclassified as an unavailable service: all five searches succeeded. No new node needs additional searches.

## Review by NP

I read Stacks more-morphisms.tex at lemma-descent-connected-fibres (Tag 057I), including the paragraph after equality over W to determine precisely where finite locally free becomes necessary. I also read the full statement and proof of lemma-base-change-connected-along-section (055M), and the section-component argument leading to lemma-connected-along-section-open (055R). I read morphisms.tex at lemma-base-change-flat (01U9) and lemma-base-change-finite-presentation (01TS). No SGA source is used. There are no new-node sources to audit.

For step 1, I opened lem-weil-pbc-flat-morphism-base-change: it states flatness of the second projection for an arbitrary base change, so it applies to p without assuming p flat. I opened lem-weil-pbc-qcqs-morphism-permanence and used exactly clause (3), which preserves the whole finite-presentation condition, including quasi-compactness and quasi-separatedness. The fibre identification is written from the universal property in def-pc-fibre-product and the fibre definition in def-pc-scheme-fibre; no point set of a product is silently identified with a product of point sets. I read def-pc-geometrically-irreducible, whose statement explicitly defines geometrically reduced for every field extension. The tower kappa(b) to kappa(z) to L therefore proves the new geometric reducedness directly. The section equations follow from the two product projections.

For step 2, I opened lem-trf-flat-reduced-section-component-open and checked all its hypotheses against step 1: schemes, flatness, full finite presentation, section and geometric reducedness of every fibre. It gives exactly openness of C. I opened def-pc-base-change; its last-factor comparison explicitly identifies X_R with Y times_Z R. I opened lem-sbc-section-component-cartesian and checked that it requires local finite type, not smoothness or geometric reducedness. Local finite presentation implies local finite type by the finite polynomial generators, as written in the step using def-sbc-locally-finite-presentation. Both section identities and their compatibility with a_i are the product equations. Hence its conclusion really is the desired equality a_i^{-1} C = C(h,s_i). I declared this off-unit generic Tag 055M tool in split_report.tool_uses rather than silently changing the route. The other two off-unit result inputs in step 1 are existing Mathlib leaves.

For step 3, I reopened the three cited definition statements. The fibre is the field extension of X_b0, so the all-field-extensions definition of geometric connectedness applies. The sections give actual points of this fibre. A connected space's connected component at either point is the whole space, by maximality. For step 4, the two explicit inverse images are open by continuity of scheme morphisms; there is no inference from pointwise incidence to a single neighbourhood without a formula. The same formula gives both image inclusions. For step 5, the loci are already identified with components in step 2. The step proves connectedness of their union from the absence of a separation and then uses maximality, rather than invoking an unstated relative comparison. This is a few-line elementary topological argument, corroborated by the Mathlib component equality hits.

I checked delivery-errors B--E point by point. There are no new statement-only nodes, no invented definitions, no relabelled clause nodes, no unrecorded searches, no proof citations to definitions for theorem content, and no long non-elementary step (all five steps are below 700 characters). The substantial facts are cited existing statements, not borrowed internal proofs. Each citation has a verbatim quote in citations.json, checked locally by substring membership against its actual statement. Every proof use occurs in proof_deps; dependencies are existing, unmerged nodes and none is a descendant of this item. The server dry run will independently check the graph and route.

Small cases checked: Z empty gives Y and R empty and W empty; an empty overlap fibre is contained in W without needing any point; an infinite overlap fibre is contained pointwise in the same open W; a disconnected fibre away from b0 causes no problem, because W retains only the incidence points; coincident sections give W=R since each section lies in its own fibre component. Empty X_b0 cannot coexist with a point r over b0, because the induced sections would give a point of that fibre; thus there is no concealed nonemptiness assumption. All fibres in step 5 are compared over the same r, with the correct residue-field extension.

## Unfinished work

None in this item's one-level stage-1 split. No Lean was written, no compiler or build was run, and the shared repository and launcher were not modified.

## Dry-run repairs

The first dry run rejected two quotes of the fibre-product universal property as shorter than 40 characters. I replaced both by the full verbatim definition, including the universal test maps; no proof or dependency change was necessary.
