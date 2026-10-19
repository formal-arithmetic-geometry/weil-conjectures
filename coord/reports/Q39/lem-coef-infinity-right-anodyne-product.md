1. Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-right-anodyne-product.json`: existing item, statement unchanged, seven-step split; no exact Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-right-anodyne-saturation.json`: new statement-only node, unsplit; no Mathlib match. It states two-variable closure for an arbitrary weakly saturated class W.
- `dag/nodes/sec-six-functors/lem-coef-infinity-right-prism-boundary.json`: new statement-only node, unsplit; no Mathlib match. It states the explicit finite horn filtration, rather than merely asserting that the boundary case of the item holds.
- `citations.json`: eleven entries, one verbatim statement quotation for each step/node pair.

The unlanded `lem-coef-infinity-right-horn-retract.json` from the earlier sandbox attempt was removed: its short vertex-formula argument is now item Step 5. No shared repository, source checkout, launcher, unit or chapter file was edited. Scratch scripts and `small-cases.log` are confined to this item sandbox.

2. Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, right-anodyne terminology, prism, weak saturation, pushout-product terminology and Proposition 4.2.5.3 returned no candidate declaration. No project Lean statement matching either new helper was found. The upstream master checkout was read as reference material only, never as evidence of a completed proof.

3. WANTED

WANTED: archival copy of Kerodon Proposition 4.2.5.3, tag 0153, for the item and `lem-coef-infinity-right-anodyne-saturation`; https://kerodon.net/tag/0153.

WANTED: archival copy of Kerodon Lemma 3.1.2.12, tag 00TH, for `lem-coef-infinity-right-prism-boundary`; https://kerodon.net/tag/00TH.

WANTED: archival copy of Kerodon Lemma 3.1.2.10, tag 00TG, for item Step 5; https://kerodon.net/tag/00TG.

WANTED: archival copy of Kerodon Proposition 1.5.5.14, tag 0077, for the boundary-generation argument in item Step 4; https://kerodon.net/tag/0077. The existing Mathlib boundary-cell node is reused.

All four online pages, including their proofs, were actually read. These are Kerodon tags, not the unrelated Stacks tags. Stacks is not a source for this one-sided simplicial combinatorial theorem. No literature was downloaded or written. The proof is marked agent-origin because these references are not archived under literature/.

4. What was wrong and what changed

The existing item statement is correct and has been retained byte for byte. The chapter/unit route and all maintainer metadata are retained. I read the three levels in SETUP.md, the unit and chapter records, the original ancestor proof and its current main-20261015 proof file. This item is below the finite-shape enhancement branch of paragraph 2 of `prop-coef-integral-exceptional-adjoint`; it is not the key node of the unit. There is no unit realization edit or off-unit theorem tool use.

The earlier sandbox attempt had unreliable descriptions of search hits, a new elementary horn-retract node, incomplete helper ancestry lists (missing the item at the front of via), a helper using “right anodyne” without introducing it, and a proof-style explanatory clause in an unsplit statement. I replaced its new-node search records with the actual results of fifteen new msearch.py calls at 2026-10-16T15:23 UTC, including two semantic phrasings per concept. Every retained search record copies its tool/query and actual logged hit names, count and digest. No unavailable service was recorded as a failed mathematical match. The old sandbox log was not used as evidence for these new records.

The saturation helper now has an arbitrary weakly saturated W, introduces its notions, and states only its two closure assertions. In particular it no longer asserts literally that the pushout-product construction preserves transfinite composites: the correct general argument filters the output composite by pushouts of the successor pushout products. That is the substantive closure result the helper leaves to its future split.

The prism helper now gives all X_q, all attaching horns, the shuffle maps sigma_q and the pushout squares, faithfully following 00TH. Its right vertical map is the factorization into X_{q+1}; the statement explicitly distinguishes this map from its composite into the whole prism. The item itself deduces right-anodyneness from this filtration. The horn retract uses the explicit monotone map r(0,t)=t, r(1,t)=max(a,t), verifies its image on both pieces of the source, and writes both retraction equations through the vertex-0 section. The iterated pushout-product identity is proved by displaying the common three-subset union.

The final paragraph of 0153 mentions m>0 when reducing to boundaries, whereas 0077 includes m=0 as well. The missing zero-dimensional check is supplied explicitly: the empty boundary gives the generating right horn Lambda_1^1={1} -> Delta^1. This is a small omitted case in the source proof, not a false item statement or a change of hypotheses.

5. What could not be finished

Nothing required for this one-level split remains. The two new non-Mathlib statements remain unsplit, as required by the brief. The next worker should independently read the split and the cited sources before delivery. No Lean code, compiler, Lake command or build was run; no delivery was pushed.

## Not duplicates

lem-coef-infinity-right-anodyne-saturation vs lem-coef-infinity-right-anodyne-product: both cite Kerodon 0153, but the new node proves closure of a preimage class for arbitrary weakly saturated W. It never asserts membership for a generating horn or that all right-anodyne maps satisfy the product assertion. Steps 3–6 of the item supply that missing combinatorial argument.

lem-coef-infinity-right-anodyne-saturation vs lem-coef-infinity-pushout-join-saturation: the existing node is for the simplicial join and the inner-anodyne class. The new one is for the Cartesian product and arbitrary weakly saturated W. A join is not a Cartesian product, and the existing statement cannot be specialized to give it. I read both statements and the existing join proof.

lem-coef-infinity-right-anodyne-saturation vs lem-coef-sset-anodyne-pushout-product: the existing Mathlib leaf proves membership in the Kan-anodyne lifting class. It does not state the two closure assertions for arbitrary W, and Kan-anodyne membership does not imply right-anodyne membership.

lem-coef-infinity-right-anodyne-saturation vs lem-coef-inner-anodyne-pushout-product: the existing Mathlib leaf concerns inner-anodyne maps, whereas the new closure theorem applies to arbitrary W and is not a product membership theorem.

lem-coef-infinity-right-prism-boundary vs lem-coef-infinity-right-anodyne-product: the new node is the explicit finite filtration of a fixed simplex prism, including the specified attachment maps. The item states no such filtration and still needs the arbitrary-monomorphism skeletal reduction, explicit horn retract, reassociation and saturation argument.

lem-coef-infinity-right-prism-boundary vs lem-coef-infinity-monomorphism-boundary-cells: the existing Mathlib leaf attaches boundary inclusions to an arbitrary simplicial monomorphism. The new node attaches nonzero-index horns to one specific prism relative to its endpoint and boundary; the existing conclusion does not give those horn indices, finite length or maps.

lem-coef-infinity-right-prism-boundary vs lem-coef-infinity-anodyne-cocones: the existing statement concerns joins, inner-anodyne join products and coherent cocone restriction, not a Cartesian simplex prism filtration.

Before revising these helpers I searched the whole DAG by right-anodyne/product/prism/saturation terminology and tags 0153, 00TG, 00TH. `tools/blueprint_refs.py search` returned no imported blueprint node for “right anodyne”, “weakly saturated”, “prism”, “0153” or “00TH”. The helpers have from.node = prop-coef-integral-exceptional-adjoint, from.place describing its paragraph 2 branch and the exact Kerodon input, and via = [this item] followed by the item's inherited via. All same_as fields are empty because no blueprint equivalent was found. The two definition nodes and the existing boundary-cell Mathlib leaf are reused, not recreated.

## Review by Q39

I reread delivery-errors B–E with the final JSON and source statements open. For the item I read Kerodon 0153 in full: its proof first fixes the second monomorphism, reduces to a right horn, retracts that horn from an endpoint prism using 00TG, reassociates the pushout products, and then reduces the other variable to boundaries by 0077 and 00TH. That is exactly the route of the final split. Both maps are small simplicial monomorphisms; only the first is required right anodyne, and the same canonical union inclusion is the conclusion. No Kan-anodyne or inner-anodyne hypothesis has been substituted for the right-anodyne one.

For the new saturation node I read the two closure assertions in the proof of 0153 and checked that their proof needs only weak saturation, not the particular generators of the right-anodyne class. For example, a continuous chain X_alpha inside X_lambda gives output stages (X_alpha times L) union (X_lambda times K); each successor is a pushout of the corresponding successor pushout product and limits are unions. The analogous stages in the other variable work the same way. Pushouts add the degreewise complement product, and section/retraction squares act on each coordinate. This verifies the arbitrary-W generalization and explains why the result is a closure lemma rather than an item clause. I checked W=all maps, W=isomorphisms, either fixed map an identity, and empty domains; none requires a horn hypothesis on the other input. The statement has no hidden proof and no dependence on the item.

For the new prism node I read 00TH's statement and shuffle construction. Every attachment is Lambda_{q+1}^{m+1}, so its index is strictly positive including the final outer horn. I checked that sigma_q factors through X_{q+1}, that the preimage of X_q is exactly this horn, and that all product simplices lie in one of the shuffles. Exhaustive finite-chain checks in `check_small_cases.py` passed 3,048 inverse-image tests for m=0 through 6. This includes the empty-boundary base case. The helper does not merely rename the right-anodyne conclusion: it provides the finite pushout-square filtration used to derive it.

I opened every statement cited by the item's steps, and copied the part used into citations.json. Step 1 uses the standard-simplex/horn/degreewise-product definition and the ordinary colimit universal property; its union and coordinate-functoriality argument is written out rather than taken from a definition node as a theorem. Step 2 uses exactly the two closure assertions of the new saturation node, applied to W defined by the existing right-anodyne definition. Step 3 uses exactly the finite pushout-square filtration of the new prism node and the generators/closure operations in that definition. Step 4 uses the existing boundary-cell node's full relative filtration statement, not a purported horn filtration, and the saturation helper's fixed-first-variable assertion. The well-ordering, successor pushouts and limit stages for a coproduct of cells are written out in that step; the empty coproduct is explicitly covered.

Step 5 uses the exact horn definition (a missing vertex other than a) to check the explicit retraction from 00TG. Because r changes only vertices to a, it cannot reintroduce a missing vertex v different from a; on the endpoint-1 piece it misses 0 since a>0. The vertex-0 section proves both identity equations. Finite-chain tests checked monotonicity, preservation of the horn on the whole prism source, and the section identities in 9,447 cases for n=1 through 6 and every allowed horn index. This short argument now belongs to the item, so no elementary helper is left.

Step 6 relies on the already established functoriality and the result of Step 4, and cites the right-anodyne definition for its retract and isomorphism closure. The two triple-product domains are explicitly the same union; no non-elementary transport lemma is hidden there. Step 7 invokes the minimality of the generated right-anodyne class, exactly as that definition states. The other steps have already established its saturation and generator hypotheses. The proof-dependency list is exactly the union of the seven uses lists, all cited nodes exist and are unmerged, and neither new helper depends back on the item.

For the Mathlib audit I read the returned semantic and Loogle hits and the pinned source of the Kan and inner pushout-product theorems, the abstract Leibniz functor/lifting adjunction, product-simplex coordinates, and the HornColimits declarations. Generic closure, horn face or coordinate lemmas do not supply either full new statement in one specialization. The current Mathlib boundary-cell leaf is reused. There is no project Lean attachment. All new statements introduce their data and use the actual definition nodes for those notions; all unsplit proofs and proof-dependency lists are empty. The item statement, chapter and unit remain unchanged, the new nodes have full provenance, and the review found no statement dispute, missing hypothesis, circular citation or forbidden source route.

The brief's dry-run command with a trailing dot is rejected by this installed deliver.py, whose usage accepts only group, item and --no-push. The documented command without that dot is used for the required preflight. This is an invocation discrepancy only; the delivery script is unmodified.

## Second reading by Q39

- Item statement: compared hypothesis by hypothesis with Kerodon 0153, Proposition 4.2.5.3, and the existing right-anodyne definition; PASS, exactly its right-anodyne assertion, with no added condition on the second monomorphism.
- Step 1: checked against the two cited definitions; PASS, the intersection and union universal property prove the asserted pushout and coordinate functoriality in each degree.
- Step 2: checked both clauses of lem-coef-infinity-right-anodyne-saturation and def-coef-infinity-right-anodyne against Kerodon 0153; PASS, all fixed inputs are monomorphisms and the generated-class reduction is valid.
- Step 3: checked the complete prism helper statement against Kerodon 00TH, assertions (a),(b); PASS, every attaching index q+1 is positive, including m=0 where the source is {1}.
- Step 4: checked the cited boundary-cell node statement and Mathlib Skeleton.lean:428-446 against Kerodon 0077(b); PASS, the stated relative sequence supplies precisely the needed boundary attachments, and the displayed serialization supplies coproduct closure.
- Step 5: checked the horn definition and the vertex formula against Kerodon 00TG; PASS after expanding monotonicity across the two levels and defining the map on every simplex with its operator compatibility. The section identities and omission of a vertex other than a establish the arrow retract, including n=1,a=1.
- Step 6: checked the retract operation of the cited right-anodyne definition and the explicit union against Kerodon 0153; PASS, both domains give the displayed three subsets, and Step 4 applies to the monomorphism h from Step 1.
- Step 7: checked minimality against def-coef-infinity-right-anodyne and the preceding saturation/generator results; PASS, this closes the argument for the original maps.
- New node lem-coef-infinity-right-anodyne-saturation: checked against the two weak-saturation reductions in Kerodon 0153 and the cited definitions; PASS, a genuine closure input, neither an elementary two-line consequence nor a restatement of the item. Its arbitrary-W generalization is valid: for a continuous chain A_alpha inside A_theta use (A_alpha times L) union (A_theta times K); successors are pushouts of theta for the successor inputs and limits are unions. Pushing out an input pushes out its theta map, and arrow retractions act coordinatewise. The same formulas with the coordinates interchanged prove the second assertion. Identity inputs, empty domains, W=all maps and W=isomorphisms produce no counterexample.
- New node lem-coef-infinity-right-prism-boundary: checked every index, endpoint, shuffle formula and pushout orientation against Kerodon 00TH; PASS, it supplies the finite filtration data rather than merely restating a right-anodyne conclusion. For m=0 it attaches Lambda_1^1; for m=1 it attaches Lambda_1^2 followed by Lambda_2^2. The required inverse images equal the specified horns.

Independent duplicate and Mathlib audit: searched the shared DAG by tags and right-anodyne/prism/saturation terminology and the whole imported blueprint with blueprint_refs.py (zero blueprint matches for right anodyne, prism and weakly saturated). Read the existing join-saturation, Kan pushout-product, inner pushout-product and boundary-cell statements. None duplicates either helper. Ran six fresh msearch.py queries with different vocabulary, including general bifunctors/Leibniz products and shuffle simplices; all actual records are in searches.jsonl and the relevant three records per helper are appended to its mathlib_searches. Read the returned relevant source statements: MorphismProperty cobase-change results, ParametrizedAdjunction.lean:37-171, Monoidal/PushoutProduct.lean:105-175, ProdStdSimplex.lean:34-90, and HornColimits.lean:30-130. They give components of these arguments, but neither complete helper in one specialization. No new Mathlib leaf or project Lean attachment was found. The existing boundary-cell Mathlib leaf remains reused.

The complete statements of all six nodes cited by the proof were opened. All eleven citations.json quotes are verbatim and support their actual use; no citation changed. Both new nodes are self-contained statement-only nodes with empty proofs and proof dependencies, single-escaped TeX, source labels and definition dependencies. No cycle through the item is introduced. The current main-20261015 ancestor proof, the inherited unit and chapter, GOAL.md and coord/dag-sync.md were read; the split serves the same finite-shape branch of the displayed mapping adjunction. No SGA route is used. No statement dispute was found.

Changes: expanded only Step 5's elementary monotonicity/simpliciality justification; added the independent search evidence to both helpers; appended this second-reading record. All first-worker sections, statements and citations remain in place. Reran the finite-chain checks: 3,048 prism inverse-image checks and 9,447 retraction checks passed, as did exact dependency and verbatim-citation checks. These finite checks supplement the source and proof review; they are not claimed as proofs in arbitrary dimension. No Lean, compiler, Lake, shared-repository mutation or live-launcher edit was performed.
