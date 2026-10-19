# Q105 current repair report

Item: lem-coef-left-fibration-colimit-realization. Stage 1 repair, 2026-10-17. The following is the current delivery report; the retained earlier reports below describe historical payloads and counts.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-left-fibration-colimit-realization.json`: repaired split, ten steps; unchanged statement and Lean record. Former step 7 is replaced by steps 7-9; the old final step only updates its step-number reference.
- `dag/nodes/sec-six-functors/lem-coef-quasicategory-ordinary-nerve-functors.json`: new statement-only, unsplit lemma; no complete Mathlib match. It identifies the edge presentation with the mapping-space homotopy category, including the full ordinary-nerve functor comparison and its simplicial parameters.
- `citations.json`: all 14 step/dependency pairs, with verbatim statement quotations.
- `report.md`: current repair and review, followed by the retained historical reports. Earlier sandbox scripts and `searches.jsonl` are retained.

New nodes: 1. New Mathlib leaves: 0.

## Attachments

None. The read-only slopmaster2 project has no declaration found by the item blueprint tag or the ordinary-nerve/homotopy-category search that states either complete assertion without sorry. The stage-2 statement and review already recorded on the item remain byte-identical; their existence is not an attachment of a completed proof.

## Sources and WANTED

WANTED: Lurie, *Higher Topos Theory*, Sections 1.2.2-1.2.3 and Proposition 3.3.4.5, for the new node and item. The existing online source is https://people.math.harvard.edu/~lurie/papers/HTT.pdf; no copy was downloaded. I read the right mapping-space definition, Proposition 1.2.2.3, the nerve adjunction in Proposition 1.2.3.1, the explicit edge/triangle presentation on printed p.29, Proposition 1.2.3.9 and its proof on printed pp.32-33, and Proposition 3.3.4.5 with its proof on printed pp.219-221. The new statement is an agent-formulated consequence, with its parameter comparison spelled out; it is not misattributed as the literal text of one proposition. No Stacks tag states this quasicategorical result.

I also read the statement of existing `lem-coef-localization-homotopy-category`, and consulted its Cisinski source https://cisinski.app.uni-regensburg.de/CatLR.pdf, Theorem 1.6.6 and Remarks 7.1.4-7.1.6. This is the already-existing theorem used for the second hidden argument. The original agent proof route via function complexes, model localization and saturation is retained. The current blueprint ancestor's mapping-complex paragraph, the chapter record and the assigned unit record were read; no chapter or unit record was changed and no SGA source is used.

## What was wrong and what changed

The human returned the 2547-character former step 7 because it hid non-elementary nerve/functor and localization comparisons. These now have explicit theorem citations: new `lem-coef-quasicategory-ordinary-nerve-functors` in step 7 and existing `lem-coef-localization-homotopy-category` in step 8. Step 9 retains only the application of those results, the inverse equations testing an isomorphism, and the existing model-localization detection theorem. No conclusion of the item was moved into a subsidiary node: neither supporting lemma mentions left fibrations, right cones, or colimits of spaces.

I continued the preserved interrupted repair rather than starting over. Comparison with the current shared node found changes only in proof, proof_deps, split_report and status; statement, statement dependencies, provenance, chapter/unit and the complete Lean and reviewed_lean fields agree. The first six steps are identical and the final original step differs only in its reference to step 9. The first resumed dry run caught a stale text citation to the deleted duplicate localization node; I replaced it with the existing node named in uses. The corrected dry run passed. I corrected the retained Mathlib candidate's product-comparison line reference to 463-469 after reading the pinned source.

## Mathlib searches and blueprint search

I reused and read all nine preserved `searches.jsonl` records and their candidate source results. The new node records the exact tool/query texts from those executed searches. The first LeanSearch, three LeanFinder searches, two Loogle searches and two grep searches were successful; the second LeanSearch explicitly reports service rate limiting and retains verdict unavailable. The two localization queries are retained as search history of the extraction that was replaced by an existing node. No unavailable service was treated as evidence of absence, and no unexecuted search is recorded.

The substantive candidate declarations read are CategoryTheory.nerveAdjunction (NerveAdjunction.lean:396-397), CategoryTheory.hoFunctor.isIso_prodComparison (same file:463-469), SSet.Truncated.HomotopyCategory.functorEquiv (same file:288-305), and the edge-quotient definition in HomotopyCat.lean:20-38. The source also supplies finite-product preservation. They do not give the node's comparison with components of the fixed right-pinched mapping spaces, so the full node is unsplit with mathlib_candidate, rather than falsely declared absent in every clause or falsely declared a leaf.

Whole-DAG searches and whole-blueprint searches for homotopy category and ordinary nerve were checked, along with the ancestor command. No imported blueprint statement gives the entire new lemma. The current ancestor remains prop-coef-integral-exceptional-adjoint with the retained via chain plus the item prepended for the new node.

## Not duplicates

- lem-coef-quasicategory-ordinary-nerve-functors vs lem-coef-localization-homotopy-category: the new node gives the edge-presentation/mapping-space identification and the parameterized isomorphism Fun(C,N(D)) = N Fun(hC,D); the existing node gives the ordinary localization induced by an arbitrary coherent localization and only defines its hC using edge homotopy. The new node imposes no localization hypothesis and asserts no localization conclusion.
- lem-coef-quasicategory-ordinary-nerve-functors vs lem-coef-coherent-nerve-comparison: the existing node compares enriched mapping spaces with those of a coherent nerve and supplies the Bergner/Joyal comparison; it does not identify full functor simplicial sets with ordinary nerve targets.

## Review by Q105

I checked the returned defect against the actual former step, rather than merely shortening its wording. The two hidden arguments are now statements of separate cited nodes. The new node is self-contained: C is a quasicategory, D is an arbitrary ordinary category, universes contain all functor categories, the edge relations and the map eta are specified, and naturality covers parameter ordinals and precomposition. Its only statement dependency defines its simplicial sets, nerves, internal Fun and right-pinched Map. Its statement contains no proof, proof_deps or construction deferred as data. All original non-elementary steps and all three replacements have fewer than 2000 characters (largest 1496).

The mathematical argument underlying the new node was checked as follows. Right-pinched Map has edges precisely triangles with the initial short edge degenerate; its components yield the corresponding edge-homotopy relation, with the dual convention identified by horn fillers. The edge presentation and Proposition 1.2.3.9 identify this quotient with the ordinary homotopy category. A map to an ordinary nerve is determined by consecutive edges, with triangular relations exactly enforcing functoriality. In C times Delta^n, an edge class is a C-edge class together with its unique ordered parameter arrow, and paired triangular fillers enforce composition; projections give the canonical product comparison. Thus maps with parameter Delta^n correspond to functors hC times [n] to D, respecting parameter restriction. This is the proof route for the future split of the new node; it is recorded here, not hidden in its statement.

For C empty both functor simplicial sets are terminal and h(C times Delta^n) is empty; for D empty they are empty unless C is empty. For C=N(A), edge relations give A exactly, and the formula reduces to the ordinary nerve of the functor category. For C a Kan groupoid the target functors factor through its fundamental groupoid, consistent with the mapping-space quotient. n=0 recovers the adjunction and n=1 recovers all natural transformations, not just invertible ones. These tests rule out replacing the full Fun by its core or claiming only a bijection on vertices.

For step 1 I checked the cited right-anodyne generators and the explicit cone filtration, including the final-vertex horn in dimension 1. Step 2 uses the actual restriction equivalence for arbitrary simplicial bases from lem-coef-infinity-anodyne-cocones and the target category of spaces from lem-coef-space-transport-classification. Step 3 uses the internal Fun definition and retains the explicit normalized prism contraction, so its restriction is the cocone in the unchanged statement. Step 4 cites the explicit cocone dual in lem-cbc-enhanced-functor-cone-calculus; the existing proposed generic tool-use justification is retained in split_report, with no maintainer-owned approval field added.

For step 5 the transport node states the complete mapping formula, constant-product case, and pullback compatibility: the forced base coordinate identifies restriction with the actual inclusion Z_0 into Z. Step 6 uses the Kan-model, pushout-product and simplicial-model-localization statements with cofibrant sources and Kan target; its existing verification of the simplicial axiom stays intact. Step 7 uses the new node for precisely the component and entire-functor comparisons its statement now contains. Step 8 satisfies the existing localization theorem's hypotheses: the model weak equivalences contain all objects and are closed under composition; the model-localization theorem supplies the coherent universal property for every target, and containing universes make the ordinary category small. Its conclusion applies to the actual gamma, including natural transformations. Step 9 uses fibrant replacements in the fixed universe and ordinary-localization saturation with no fibrancy assumption on either endpoint; its two inverse equations are elementary. Step 10 combines these equivalences and keeps the empty-shape check.

I reread every cited statement for C4 and checked all 14 literal quotation pairs and their coverage. The overlaid dependency closure of 521 nodes has no cycle back to the item. B-E checks found no clause restatement, hidden hypothesis, invented tag, or SGA dependence. For the item, empty L yields initiality of the apex; a one-point L detects equivalence of the single arrow, and two discrete point fibers at a point apex give two components mapping to one and correctly fail. The human's statement- and Lean-preservation condition is satisfied.

## Unfinished work and validation

The single new lemma is intentionally statement-only and unsplit, ready for its own stage-2 statement and later split. No Lean source was written and no compiler, Lake or build tool was run. No mathematical part of the requested one-level repair is left unfinished.

The first resumed dry run failed solely on the stale text node name, repaired as above. The corrected server dry run exited 0 with `OK (not pushed)` at prepared commit 909d105341 and preflight passed. A final dry run is required after this report and candidate-line correction, followed by direct delivery. Only one deliver.py invocation is active at a time.

# Retained historical reports

The following text is retained from the interrupted sandbox as provenance. Its zero-new-node counts and earlier handoff instructions describe the Q33 payload, not this Q105 repair; the current report above supersedes them.

# Worker report

Item: lem-coef-left-fibration-colimit-realization. Group: Q33. Stage 1 only. Date: 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-left-fibration-colimit-realization.json`: statement node, now split into eight proof steps. Its statement, statement dependencies, chapter, unit, created provenance and inherited fields are preserved. Five newly executed Mathlib searches are appended to the inherited search records.
- `citations.json`: literal statement quotations for every dependency of every numbered step. Multiple quotations are included where a step uses two clauses.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing DAG already contains all the non-elementary inputs used in this proof. The sandbox also contains the prior dispatch markers and search log, a sandbox-only writing script, and the raw results of the five new searches; these are not additional DAG nodes.

## Attachments

None. Searched the read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for left-fibration, LeftFibration, unstraightening, homotopy-colimit and Proposition 3.3.4.5 vocabulary. No declaration states this item. The copied item has no recorded Lean declaration. General ordinary-categorical Grothendieck colimit declarations do not prove the space-valued coherent statement. No Lean was written and no compiler, Lake or build command was run.

## Sources and WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 3.3.4.5 and Corollary 3.3.4.6 (printed pp. 219-221), for lem-coef-left-fibration-colimit-realization. Read the online Harvard HTT PDF, including the complete proposition and its proof; it is not archived in `literature/`. Its three equivalent conditions include precisely our conditions (1) and (3), for an arbitrary simplicial set, without filteredness or a quasicategory hypothesis. No Stacks tag states this quasicategorical result.

The source proves the result via covariant equivalence and straightening. The delivered proof is explicitly marked `proof_origin.by = agent`: it gives the equivalent direct mapping-space proof using the existing coherent transport and right-anodyne restriction statements. It does not claim to reproduce HTT's model-rectification proof verbatim. This change is below the unit level and keeps the role of this item in the recorded HTT 5.5.4.13 factorization argument.

Read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, and both the statement and proof of the current blueprint's `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint`. The ancestor's second proof paragraph is the mapping-complex adjunction calculation. The ancestry records the general categorical foundations introduced for that calculation, including the presentability and filtered-refinement chain. This subsidiary theorem is not a separate assertion imported from that blueprint, and neither the chapter nor the unit is changed.

## What was incomplete or corrected

The earlier sandbox contained only the unsplit item and search logs, with no report, citations or proof. I completed it rather than treating its earlier searches as a finished split. There is no statement dispute: the given statement agrees with HTT, including the empty shape. I kept the explicit right-cone cocone convention and its small-total-space hypothesis.

The potential gaps were the passage from the cone vertex to the entire diagram, identification of the *actual* cocone map under that passage, and detection of weak equivalences by function complexes even when the total spaces are not Kan. Steps 1-3 and 6-7 supply those arguments. A definition of colimit alone would not justify the mapping-space criterion: step 4 explicitly cites the theorem `lem-cbc-enhanced-functor-cone-calculus`. A definition of the Kan model structure alone would not justify the mapping-space comparison or saturation: steps 6-7 cite those theorems separately.

The source for the generic anodyne pushout-product node is pinned Mathlib, and that node is reused without a new copy. Likewise no new node was made for a clause of this item or for the elementary cone filtration, curry/uncurry calculation, or inverse equations in a category.

## Mathlib and duplicate searches

All five appended searches were actually run through `/home/ubuntu/weil-launcher-nt/msearch.py Q33 lem-coef-left-fibration-colimit-realization`; the raw outputs are preserved in `current-search-results.json`, and the command appended their audit records to `searches.jsonl`. Exact queries:

- leanfinder: `A coherent cocone of spaces is colimiting if and only if the inclusion of total left fibration spaces is a weak homotopy equivalence`
- leansearch: `The homotopy colimit of a space valued infinity category diagram is computed by its Grothendieck left fibration total space`
- loogle: `"LeftFibration"`
- grep: `left.?fibration|homotopy.?colimit|unstraighten`, subdirectory `AlgebraicTopology`
- leanfinder, second phrasing: `The total space of a Grothendieck construction of a homotopy coherent diagram of Kan complexes represents its homotopy colimit`

The services returned successful responses; none was unavailable. Read the actual semantic-search hits in the pinned Mathlib checkout: `CategoryTheory/Functor/KanExtension/Adjunction.lean:211-234` (`colimitIsoColimitGrothendieck`), `CategoryTheory/Limits/Shapes/Grothendieck.lean:130-210` (fiberwise ordinary colimits), and `AlgebraicTopology/SimplicialSet/SubcomplexColimits.lean:35-70`. Their objects are ordinary categories or ordinary simplicial-set colimits; they do not state the coherent space-colimit criterion. Read the beginning of `ModelCategory/Instances.lean` as well; those model-category instances do not state the item. The zero-hit Loogle and grep queries were supplemented by the second semantic phrasing, not treated alone as a proof of absence.

Searched the entire DAG for left fibrations, total spaces, weak-equivalence detection, maps into Kan complexes and the same HTT place, and opened the candidate statements. Ran `tools/blueprint_refs.py ancestor lem-coef-left-fibration-colimit-realization`, and whole-blueprint searches for `left fibration`, `homotopy colimit` and `weak homotopy equivalence`. The four homotopy-colimit hits concern triangulated telescopes and do not state this item. The classification, right-anodyne restriction, Kan model and model-localization statements were reused. Consequently no new node needs a pairwise same-tag justification.

## Not duplicates

No new nodes. Existing generic inputs are cited, with no statement restated as a new node. The item's `blueprint.same_as` remains the searched empty list.

## Review by Q33

I read the item against HTT Proposition 3.3.4.5 (all three conditions and its proof on the online printed pp. 219-221), rather than assuming a filtered indexing category. Its total-space inclusion is indeed a weak *homotopy* equivalence, not a categorical equivalence. A coherent cocone is fixed by the interval-to-right-cone map in the statement; the proof retains that same map. No new node was created, so there is no unreviewed subsidiary statement hidden in the delivery.

Step 1 uses the definition of right-anodyne maps in `lem-coef-infinity-anodyne-cocones`. I checked the horn orientation: the omitted face of the cone simplex is the *last* face, namely the base simplex, and the available horn is the coned boundary. At dimension zero the available horn is the final vertex. Degenerate proper faces are already present from lower-dimensional stages. Thus the explicit filtration works for any simplicial set, including one with noninjective face maps; there is no nerve or quasicategory assumption. This is the elementary combinatorial argument, not an appeal to the new theorem being proved.

Step 2 uses exactly the mapping-space restriction assertion of that anodyne node, which is independent of existence of colimits and permits a simplicial base. Its target must be a quasicategory; the space-transport node explicitly supplies the infinity category presented by small Kan complexes. The same node fixes the size convention. I checked the cited statement, not merely its source or proof.

Step 3 is a simplexwise construction from the internal functor simplicial sets of `def-cbc-enhanced-diagrams-cones`. Repetition and deletion of vertices respect the formula for H, even when the initial segment already contains the cone vertex. The component at the cone vertex is the identity. Consequently composition with tau is a right inverse up to homotopy of the actual equivalence e_X in step 2. Restriction to L is exactly lambda, so the composite r_X u_X is precomposition with the specified cocone, including its coherence, and not a comparison chosen only objectwise. This corrects a possible E5 compatibility gap.

Step 4 uses the *dual* of the consequent mapping-space criterion in `lem-cbc-enhanced-functor-cone-calculus`; its statement explicitly says that the dual assertions hold for cocones and initial objects and that arbitrary shapes are permitted. Thus it proves the iff used here, whereas the definition node alone would not. This node is in unit `sk-prop-sf-cbc`; its use is explicitly declared in `split_report.tool_uses` as a generic coherent-category foundation. It replaces no geometric or coefficient step of the home unit's route.

Step 5 uses the full mapping-space formula of `lem-coef-space-transport-classification`, its constant-functor clause, and its pullback and composition compatibility. These are all explicit in its statement. A map into B times X over B has a forced B-coordinate; projecting the other coordinate is an isomorphism of simplicial sets, including n-simplices, not merely a bijection on objects. Pullback identifies the boundary with exactly Z_0, so the map is precomposition by its inclusion. This checks C4 for both the object and the arrow identifications.

Step 6 uses `lem-coef-kan-quillen-right-proper` for the actual weak equivalences, monomorphism cofibrations, fibrant objects and horn/boundary characterizations; `lem-coef-sset-anodyne-pushout-product` for its lifting theorem; and `lem-coef-simplicial-model-nerve-localization` for naturally represented mapping spaces. I checked the last theorem requires a simplicial model category, which is why the proof verifies its axiom rather than assuming it from the Kan model node. The two cases of triviality use respectively the symmetric pushout product with a boundary and the monomorphism lifting property against trivial fibrations. Every object is cofibrant since its empty inclusion is a monomorphism. The target X is Kan. Thus raw Fun(A,X) really computes the derived mapping space, even for non-Kan A.

Step 7 uses the localization universal property from `lem-coef-simplicial-model-nerve-localization` and the exact iff of `lem-coef-model-localization-detects-weak-equivalences`. The latter does not assume cofibrant or fibrant endpoints and applies to an *ordinary* localization. The proof explains why the homotopy category of the infinity localization is that ordinary localization (test its functor-category universal property against nerves of ordinary categories). The two inverse equations are written out; this is the elementary representable test for isomorphisms. All target objects needed in that test have small Kan representatives by the Kan-model replacement. Thus the tests range over the stipulated universe, and not an unjustified larger class of spaces.

Step 8 combines the equivalences already proved. I checked the empty L case explicitly: B is a point, Z_0 is empty, and the condition becomes initiality of F(v), or equivalently the weak equivalence from the empty simplicial set to Z. For L a point, a diagram is a single arrow of spaces; the criterion detects when that arrow is an equivalence. For a discrete two-point L with all three fibers points, the base total space has two components and the cone total space is contractible; the cocone is not a colimit, consistently with the criterion. For a constant empty-valued diagram both total spaces are empty and the cocone is colimiting. Taking X empty in the tests preserves the correct distinction between empty and nonempty domains. None of these checks removes any hypothesis from the item.

I checked B1-B10: no new statement-only node is improperly split, no new data definition or missing notion was introduced, no invented Stacks tag or SGA source was used, and no attachment is asserted. I checked C1-C8 by opening every cited statement; the citations file quotes those statements literally. All dependencies except the explicitly declared generic comma-calculus tool are in the item's home unit. Traversal of the current dependency closures found no path back to this item. I checked D1-D5: there is no new node to which the conclusion has been moved, and the cone-map and mapping-detection arguments are written in the item. I checked E1-E7 as detailed above; no source error or statement weakening was needed.

## Unfinished work and validation

No mathematical step is left to a new node in this split. The reused existing inputs retain their own DAG statuses. Independent second reading and delivery are intentionally left to the next worker under the brief. Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q33 lem-coef-left-fibration-colimit-realization --no-push`. The delivery tool records the accepted input fingerprint when the server preflight, DAG check and split review pass; no push is authorized for this worker.


## Second reading by Q33

Independent reader, 2026-10-17. Read delivery-errors B-E, GOAL.md, coord/dag-sync.md, the stage-1 contract, the item, every statement cited by its proof, the chapter and unit records, and the current main-20261015 ancestor proof. No agents, Lean writes, compiler commands, git commands in the shared repository, or live-project changes were used.

- Item statement: checked against the actual online HTT Proposition 3.3.4.5, all three conditions and proof, printed pp. 219-221, and Corollary 3.3.4.6; PASS. Its K is an arbitrary simplicial set, its total-space inclusion is a weak homotopy equivalence, and it requires no filteredness. The explicit interval cocone uses the same final cone vertex. The universe and small-total-space conditions specify the size in which the comparison is made; there is no change to the statement or stmt_deps.
- Step 1: checked the right-anodyne generators and join formula in lem-coef-infinity-anodyne-cocones against the right cone definition; PASS. At n=0, Lambda^1_1 consists of the final vertex. In dimension n the coned proper faces are present, and the two newly attached nondegenerate simplices are sigma and sigma star v; degeneracies introduce no extra cells. Empty L gives the identity inclusion. This explicit filtration is elementary, not an uncited cofinality theorem.
- Step 2: checked the actual mapping-space assertion of lem-coef-infinity-anodyne-cocones and the infinity category of spaces in lem-coef-space-transport-classification; PASS. Also opened Kerodon 02NR, condition (6), and checked its opposite dual for cocones. The codomain is a quasicategory, the base need not be one, and the displayed map really is vertex restriction.
- Step 3: checked the simplex operators for internal Fun in def-cbc-enhanced-diagrams-cones and the ordered blocks in def-coef-infinity-relative-cone; PASS. Cutting the initial block at the last interval-zero vertex commutes with every monotone map; later vertices all become v. At v the transformation is degenerate. Thus e_X u_X is the identity up to the unit composition homotopy and restriction gives the specified lambda. This is an elementary construction with no new theorem deferred.
- Step 4: opened the whole cone/comma mapping-space clause of lem-cbc-enhanced-functor-cone-calculus, including its explicit cocone dual; PASS. It supplies the mapping-space criterion, not merely a homotopy-category universal property. The home unit has no replacement criterion; this is a proposed generic tool use for maintainer acceptance. The split_report.tool_uses entry is the justification submitted for that decision, not a top-level tool_uses approval written by this reader.
- Step 5: opened the classification's actual mapping formula, Kan assertion, constant-product clause and base-pullback compatibility; PASS. In degree n the B coordinate is forced to be p composed with projection, leaving precisely a map Z times Delta^n to X. Pullback gives exactly Z_0, and restricting the second coordinate gives precomposition with its inclusion. The comparison therefore includes the actual arrow, not just the two mapping-space objects.
- Step 6: checked the Kan-model, pushout-product and model-nerve-localization statements in full; PASS. Also read the pinned PushoutProduct.lean:65-103, including SSet.anodyneExtensions_pushoutObjObjι. Every source is cofibrant, X is fibrant, and a trivial cofibration has the specified anodyne lifting property by the model weak factorization system. Symmetry exchanges the product factors in the boundary test; the other trivial case uses a monomorphism against a trivial fibration. Currying identifies these with exactly the simplicial model lifting axiom. Hence the natural raw/derived mapping comparison applies to non-Kan Z and Z_0. Replacements remain within the category of W-small simplicial sets.
- Step 7: checked the full functor-category localization property and the ordinary-localization saturation statement, including its absence of cofibrancy/fibrancy hypotheses; REPAIRED the compressed passage between the two localizations. The text now writes the inverse constructions between maps into N(D) and functors on the homotopy category, using edges, triangular faces and naturality squares. It then applies the cited universal property. The inverse equations g(qi)=1 and (qi)g=1 were already correct. Fibrant replacements provide all target representatives in the fixed universe, including the empty Kan complex.
- Step 8: checked both equivalences from steps 4-7 and HTT condition (3); PASS. L empty gives Z_0 empty and colimit apex empty; L a point reduces to detecting an equivalence of the single cocone arrow. For two discrete points with all fibers points, Z_0 has two components whereas Z is contractible, and the cocone is not colimiting. For all fibers empty, both totals are empty and the cocone is colimiting. X empty distinguishes empty from nonempty domains. Fields, schemes and zero modules do not occur in this simplicial statement.
- New nodes: none; B1-B7 and node-removal checks have no new statement to discharge. Rechecked existing-node candidates lem-coef-space-valued-straightening (classification over quasicategories plus strict-diagram comparison), lem-coef-infinity-cofinality-space-test (final functors between quasicategories), and lem-coef-compact-diagram-cocone-transport (filtered transport); none states this criterion for arbitrary L. No new node restates the item or an elementary step.

Changes and reasons:

1. Expanded step 7's ordinary-localization bridge so the saturation lemma has its exact hypothesis visibly established (C1, C4, E5). No other proof step was rewritten.
2. Consolidated citations.json to one verbatim statement excerpt per step/dependency pair, including the full formulas needed by steps 4 and 5. All excerpts were tested as literal substrings of the cited statements; every step use has exactly one entry.
3. Ran two independent searches through msearch.py and appended their actual audit responses to the item's mathlib_searches: LeanFinder, `A map of simplicial sets is a weak homotopy equivalence if and only if mapping into every Kan complex induces a homotopy equivalence` (8 hits), and grep, `colimitIsoColimitGrothendieck|IsColimit.*Grothendieck` (9 hits). The returned declarations read were Homotopy.lean:238-253, CofibrantObjectHomotopy.lean:84-90 and Functor/KanExtension/Adjunction.lean:213-234. They concern ordinary colimits or homotopy classes, not this coherent colimit criterion. No unavailable search was counted as a negative result. The original worker's five searches remain recorded.
4. Clarified the proposed cross-unit tool's approval status in split_report.summary and this reading; no maintainer-owned top-level tool_uses field was added. The statement, provenance, chapter, unit and blueprint ancestry are unchanged. The historical unit record still contains its old geometric/SGA description; this split does not cite that route as a proof input and uses no SGA source.

Source links read: https://people.math.harvard.edu/~lurie/papers/HTT.pdf (Proposition 3.3.4.5, Corollary 3.3.4.6) and https://kerodon.net/tag/02NR (Proposition 7.2.2.1, condition (6), opposite dual). No Stacks tag states the item, so none is invented. Validation and delivery results follow below.

Validation: the required server dry run `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q33 lem-coef-left-fibration-colimit-realization --no-push` returned `OK (not pushed)` with preflight passed (prepared commit `8e87a4fdc9`). The report now includes that result; the final unchanged payload is checked again before delivery. Citation validation covered all 12 step/dependency pairs, and the overlaid 371-node dependency closure has no path back to this item. New nodes: 0; new Mathlib leaves: 0.


## Not duplicates

- lem-coef-quasicategory-ordinary-nerve-functors vs lem-coef-localization-homotopy-category: the new node identifies the entire simplicial functor set into an ordinary nerve, including parameter simplices and natural transformations; the existing node only states that a coherent localization induces an ordinary localization on homotopy categories.

## Review by Q105

I reread the current item node, its HTT Proposition 3.3.4.5 source, the ancestor blueprint paragraph, and every cited statement. The returned defect was specifically step 7, whose 2547 characters contained two independent lemmas. I split those arguments while keeping the item statement, universes, cone convention, and the original model-localization route unchanged. The first new node, `lem-coef-quasicategory-ordinary-nerve-functors`, states the edge presentation of the homotopy category and the full identification of `Fun(C,N(D))` with `N Fun(hC,D)`, including the product-with-simplex comparison needed for transformations. I searched the whole DAG and blueprint before creating it; no existing node states those clauses. Its Mathlib searches were run with msearch.py and the returned NerveAdjunction/HomotopyCat declarations were read; they provide the homotopy-category/nerve adjunction and product comparison but not the full coherent parameterized theorem, so the node remains unsplit.

The second hidden argument is already stated by existing `lem-coef-localization-homotopy-category`, which I read in full: a coherent localization `q:N(C)→L` induces the ordinary localization `hq:C→hL`, with its universal property for functors and natural transformations. I deleted the duplicate repair node and cited this existing node in step 8. Step 7 now applies the new nerve-comparison node; step 8 applies the existing localization node; step 9 contains only the componentwise inverse equations and invokes the existing model-localization detection theorem. Every citation quote in `citations.json` is the verbatim statement of the cited node. All proof steps are below 2000 characters, with the extracted statements carrying the former inline lemmas. I checked the empty-shape case and retained the original smallness and no-filteredness clauses. No Lean, compiler, Lake, or build command was run.
