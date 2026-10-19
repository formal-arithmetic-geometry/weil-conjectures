## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-pushout-join-saturation.json`: item split into five proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-join-colimit-functoriality.json`: one new statement-only node; no Mathlib match.
- `citations.json`: five verbatim quotations, one for each proof-step use.
- `searches.jsonl`: the actual msearch records for the item and the new node.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, the blueprint tag and the terms `pushout`, `join`, `inner anodyne` and `weakly saturated`; no project declaration states this item without `sorry`. The upstream-master checkout was also searched as reference material and contains no finished declaration of this item. The only project hit was unrelated algebraic-geometry gluing code.

## WANTED

- WANTED: an archived copy of Kerodon Proposition 4.3.6.4 (tag 018J), for the two weak-saturation reductions and the join/pushout compatibility used by the item and `lem-coef-infinity-join-colimit-functoriality`. I read the online statement and proof, but it is not archived in `literature/`.

The proof origin is therefore agent-written from the online source, as required for a missing local document. No SGA source is used.

## What was wrong or corrected

The imported item was an unsplit statement with an empty proof. Its statement has the right two-variable conclusion and the required explicit join and weak-saturation conventions. I retained it exactly. I supplied the missing argument in the two variables and isolated the non-elementary construction-level fact that the simplicial join and the induced pushout-join map commute with pushouts, transfinite colimits and retract diagrams. No hypothesis was added, and no conclusion was weakened.

The source's phrase “the same argument in the other variable” is expanded as Step 5. The transfinite step explicitly uses the canonical comparison from the colimit of the theta maps to theta of the colimit, so it does not silently identify two different pushouts. The item does not assert the right-anodyne generating-horn calculation; that belongs to its dependent node `lem-coef-infinity-anodyne-cocones`.

## What remains

The one new helper node is intentionally statement-only and unsplit. It states only join functoriality and colimit comparison, not the item's inner-anodyne conclusion. No Lean code, compiler, Lake or build tool was used.

## Not duplicates

- `lem-coef-infinity-join-colimit-functoriality` vs `lem-coef-infinity-anodyne-cocones`: the existing node asserts that right-anodyne joins are inner anodyne and gives a coherent-cocone equivalence; the new node only gives functoriality and colimit comparison of the join construction, with no right-anodyne or cocone conclusion.
- `lem-coef-infinity-join-colimit-functoriality` vs `lem-coef-infinity-terminal-anodyne`: the existing node characterizes a final vertex by right-anodyneness; the new node has no quasicategory, vertex, terminality or mapping-space hypothesis.
- `lem-coef-infinity-join-colimit-functoriality` vs `lem-coef-infinity-colimit-gluing`: the existing node computes coherent colimits indexed by a pushout from three supplied colimits; the new node concerns degreewise simplicial join and pushout maps and supplies no colimit in a target infinity-category.
- `lem-coef-infinity-pushout-join-saturation` vs `lem-coef-infinity-anodyne-cocones`: the item proves only weak saturation of the class of maps whose theta map is inner anodyne; the existing node additionally proves the generating right-horn case and the cocone restriction equivalence.
- `lem-coef-infinity-pushout-join-saturation` vs `lem-coef-infinity-final-index-colimit`: the existing node is a final-index evaluation theorem for coherent colimits; the item is a two-variable simplicial weak-saturation theorem and has no final object or colimit-existence conclusion.

I searched the whole DAG and blueprint by `pushout join`, `weak saturation`, `inner anodyne`, `join colimit`, and the Kerodon tag 018J. No existing node states either the helper or the item.

- `lem-coef-infinity-join-colimit-functoriality` vs `lem-coef-infinity-pushout-join-saturation`: the helper states only functoriality and colimit comparison of the theta construction; the item concludes that the maps satisfying the inner-anodyne predicate form weakly saturated classes. The helper has no inner-anodyne predicate or saturation conclusion.

## Review by Q42

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, `GOAL.md` and delivery-errors B–E. I read the fixed chapter `sec-six-functors.json` and the recorded unit `sk-prop-sf-biduality-general.json`. The item's source is Kerodon 018J, Proposition 4.3.6.4; the current node ancestry points to the derived-coefficient-adjunction paragraph of `prop-coef-integral-exceptional-adjoint`. I also opened the complete statement of `def-cbc-enhanced-diagrams-cones`, which supplies the simplicial-set, horn and degreewise-product conventions used by the item. The item and helper statements agree with the source's ordered join construction and contain no coefficient, finiteness, nonemptiness or existing-colimit assumption.

For the new helper I checked all clauses directly from the displayed join formula. In each simplicial degree, joining by a fixed simplicial set is formed from coproducts and products, and the pushout-join domain is the corresponding pushout. Thus maps of diagrams induce maps of the theta arrows, and the canonical colimit comparison is an isomorphism. The same calculation applies after exchanging the two join variables. I searched Mathlib with leanfinder, Loogle, grep and leansearch; the hits were generic simplicial colimits and morphism-property closure, with no declaration of this join-specific comparison. The node is therefore unsplit with `mathlib_match: null`.

Step 1 fixes `k` and invokes only the helper's functoriality and identity clause to obtain the isomorphism part of weak saturation. Step 2 invokes the helper's pushout comparison and the definition of inner-anodyne closure under pushout. Step 3 invokes its transfinite-colimit comparison and the corresponding closure operation; the limit comparison is stated explicitly so no size or finite-shape assumption is hidden. Step 4 invokes its retract naturality and the retract closure. These four steps establish all clauses of weak saturation in the first variable. Step 5 repeats precisely the same four arguments after interchanging `i` and `k`, establishing the second-variable clause. Every step's only non-elementary input is the complete statement of `lem-coef-infinity-join-colimit-functoriality`, quoted verbatim in `citations.json`.

I checked edge cases: identity maps give an isomorphism theta; the empty simplicial set makes the mixed join summands vanish; `K=L` makes theta the canonical identity comparison; a one-simplex join has the expected ordered vertices; and a transfinite chain with a limit stage is handled degreewise. The proof never assumes that the monomorphisms are finite, that the simplicial sets are nonempty, or that an inner-anodyne map is a horn itself. The helper does not depend on the item, so the dependency graph is acyclic. No source statement error was found and no `STATEMENT-DISPUTED` correction is needed.

## Second reading by Q42

This is an independent second reading. The first worker's sections above are retained as its historical report; the repairs and final counts in this section supersede its five-step proof, helper-node decision and claims that the original transfinite argument was complete. Final delivery: twelve elementary proof steps, zero new nodes, zero Mathlib leaves, two citations of existing definitions. The item's statement is unchanged.

I read delivery-errors B--E, GOAL.md, coord/dag-sync.md, the worker role, stage-1 contract and brief, the recorded chapter/unit and the current main-20261015 proof of prop-coef-integral-exceptional-adjoint (paragraph 2, the displayed derived coefficient adjunction). I independently opened Kerodon 018J, Proposition 4.3.6.4, including its full proof. This is a Kerodon tag, not a Stacks tag: no Stacks .tex statement is being invoked. The source first fixes f and asserts weak saturation in g, then fixes a boundary inclusion g and asserts weak saturation in f. These closure arguments use only the pushout-join construction and inner-anodyne closure, so they apply to every fixed monomorphism as in the item; no right-anodyne hypothesis is needed for the closure assertions themselves. The ordered join, monomorphisms, inner-horn range and weak-saturation operations agree, hypothesis by hypothesis. The right-horn generator calculation belongs to the existing parent lem-coef-infinity-anodyne-cocones and is not imported into this item. The online source remains WANTED as above; proof_origin.by remains agent. No source or item statement dispute was found.

Original-step audit, with the cited helper and both definitions open:

- Original Step 1: checked against the join formula and the helper's actual statement; repaired the claim that empty maps give identities. For i=k=(empty -> point), theta is the two-vertex boundary inclusion into the edge, not an identity. Only isomorphisms are used for the weak-saturation base case.
- Original Step 2: checked against degreewise set pushouts; its conclusion is correct but the cited helper's arrow-diagram/colimit wording does not supply the specific cobase-change square. Replaced it with the explicit complement calculation in final Step 5, allowing an arbitrary, possibly noninjective attaching map.
- Original Step 3: checked domains and codomains of successive theta maps; rejected the claimed raw transfinite composite. With X0 empty, X1 a point, X2 two discrete points and k=(empty -> point), theta(X0 -> X1,k) ends at an edge, while theta(X1 -> X2,k) starts at an edge plus an isolated vertex. They cannot be composed. Final Steps 6--7 instead compose pushouts of these maps in a single ambient join.
- Original Step 4: checked against functoriality on the pure and mixed join summands and the pushout universal property; its retract conclusion is correct. Final Steps 3 and 8 now write the induced section/retraction and the identity composite.
- Original Step 5: checked against the nonsymmetric ordered join; rejected the instruction to repeat the previous argument as insufficient (E5), and replaced it with the second-variable pushout calculation, a separately defined filtration and its retract calculation in final Steps 9--12. No symmetry isomorphism or reversal of vertex order is used.

Final-step audit (each step is elementary only for the specific written calculation; the proof does not cite the statement or proof of an unproved helper):

- Step 1: checked against the complete statements of def-weil-pbc-simplicial-set and def-cbc-enhanced-diagrams-cones; the natural map from a simplex is given explicitly and tests injectivity; quotient/union operators and their universal maps are supplied. Pass.
- Step 2: checked in every pure and mixed summand of the item's displayed join formula; the intersection is A star K and the two pure summands are entirely in the domain, even for empty sets. Pass.
- Step 3: checked the maps on both coordinates against ordered restriction, identity and composition; either isomorphism makes the mixed domain full. The resulting inner-anodyne assertion follows from the item's inline definition. Pass.
- Step 4: checked the degreewise pushout decomposition, injectivity in an ordinal colimit and cancellation through a retract; this verifies that the classes remain classes of monomorphisms after all closure operations. Pass.
- Step 5: checked the actual cobase-change square against B'=A' disjoint-union (B0 minus A0); the complementary mixed pairs are unchanged and all pure simplices already occur. The pushout is valid even when A0 -> A' identifies elements. Inner-anodyne closure is its defining closure in the item. Pass.
- Step 6: checked the filtration P_alpha and both displayed intersection/union equalities degreewise; in a mixed summand these are ordinary distributivity of intersection over union for nested X_alpha subsets. Each successor is a pushout of the stipulated inner-anodyne theta map, with the correct common source. Pass.
- Step 7: checked continuity by locating the X-coordinate of each mixed simplex at an earlier stage; endpoints are exactly the source and target of theta for the whole composite. The zero-length chain is an isomorphism, not an empty colimit. Pass.
- Step 8: checked the two induced arrow squares and their identity composite using Step 3; retract closure, together with the earlier isomorphism/pushout/chain checks, proves the first class weakly saturated. Pass.
- Step 9: checked the second-variable cobase-change square against L'=K' disjoint-union (L0 minus K0); the new mixed pairs and both pure summands give its pushout without changing join order. Pass.
- Step 10: checked the separately defined Q_alpha and F_alpha in B star Y_lambda; the displayed intersection and union identify its successor map as the required pushout in the second variable. Pass.
- Step 11: checked continuity using the Y-coordinate, the two endpoints and lambda=0; transfinite closure is applied to a genuine continuous composable chain. Pass.
- Step 12: checked the section and retraction on the second coordinate and on both pure summands; their composite remains the identity on the pushout domain, proving the second class weakly saturated. Pass.

New-node audit:

- lem-coef-infinity-join-colimit-functoriality: opened its full statement, both definitions, and Kerodon 018J. It is statement-only, but its reference to join conventions in def-cbc-enhanced-diagrams-cones is inaccurate (that definition supplies simplicial sets and horns, not joins), and its colimit-of-arrows comparison does not provide the successor-pushout filtration needed for the original Step 3. All facts actually needed here have short explicit degreewise proofs, so I removed this uncommitted node under B3, C2 and the new-node minimization rule. No new node remains to check against B1--B7.

Independent duplication and Mathlib checks: searched the whole DAG by 018J, pushout-join, inner anodyne, weakly saturated and Leibniz, and ran blueprint_refs.py search for join, pushout-join, inner anodyne and 018J across the whole imported blueprint. The latter three have no blueprint-node matches; the broad join search's adjoint-related matches do not state this lemma. Read the statements of lem-coef-infinity-anodyne-cocones (a parent that cites this item, hence unusable here), lem-coef-infinity-terminal-anodyne, lem-coef-infinity-colimit-gluing and lem-coef-infinity-final-index-colimit; none supplies this closure calculation. The remaining dependencies are two definition nodes, so no cycle or off-unit theorem is introduced.

I ran fresh msearch queries in Mathlib's general vocabulary: leanfinder for a separately cocontinuous bifunctor and its pushout product; loogle for IsStableUnderCobaseChange; grep for Leibniz/pushoutProduct/joinFunctor/sSetJoin/def join in CategoryTheory; grep for join/Join/star/Leibniz in AlgebraicTopology/SimplicialSet; and leansearch for the Leibniz construction of the ordered join preserving cobase change and weak saturation. The actual records are appended to searches.jsonl and to the item's mathlib_searches. I read PullbackObjObj.lean:12--41,72--142, ParametrizedAdjunction.lean:12--22,39--167 and Inner/PushoutProduct.lean:14--45,50--105. The generic API constructs a Leibniz pushout from a supplied bifunctor, while the simplicial inner-anodyne pushout-product theorem uses the cartesian tensor. No ordered simplicial-join saturation declaration or one-line specialization was found. Searches in both project-source checkouts likewise found no ordered-join implementation; the master checkout is reference material, not a finished-proof attachment.

Small cases checked explicitly: degree zero has no mixed summand and theta is bijective on vertices; degree one has complementary pairs (B0 minus A0) times (L0 minus K0). When both maps are empty -> point this adds the edge between two existing vertices, exposing the original empty-map error without disputing the item. If either map is an identity (including empty -> empty), theta is an isomorphism. Joining with an empty simplicial set returns the other simplicial set. Filtrations of length zero and one have the stated endpoints, and a nonzero limit is a union because a mixed simplex has only one varying coordinate. For a noninjective attaching map, take A0={a,b}, B0={a,b,c}, A'={z} and send both a,b to z: B'={z,c}, so precisely the c-coordinate mixed pairs are added on both sides of Step 5. The second-variable calculation has the corresponding literal set decomposition. No coefficient field, scheme, finiteness or nonemptiness assumption enters this simplicial lemma.

Changes and reasons:

- Kept the item's statement, ancestry, source and first worker report sections; its two conclusions are correct and used verbatim by the parent.
- Removed the uncommitted helper and all its citations: its needed content is elementary, and its transfinite comparison was insufficient for the claimed argument.
- Replaced the raw-composite assertion by the explicit continuous P_alpha and Q_alpha filtrations with pushout successor maps and checked limit stages.
- Removed the false empty-map assertion; retained precisely the isomorphism base cases required by weak saturation.
- Expanded the entire second-variable argument, including pushouts and retracts, to avoid E5 and any assumed symmetry of ordered joins.
- Added the elementary check of preservation of monomorphisms and the coordinate description of all induced join maps.
- Regenerated citations.json with the two verbatim definition excerpts actually used by final Step 1; no citation relies on a node's proof rather than its statement.
- Appended independent search records and updated split_report to the final twelve-step, zero-new-node implementation. No Lean file was written and no compiler, Lake or build tool was run.
