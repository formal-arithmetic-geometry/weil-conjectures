## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-path-fibration-replacement.json`: existing statement, split in six steps; no exact Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-space-endpoint-evaluation-fibration.json`: new unsplit statement-only auxiliary node; no exact Mathlib match.
- `citations.json`: one verbatim statement extract for every step/node citation.
- `report.md`: this report. The required search wrapper maintains `searches.jsonl`.

One new statement-only node and no Mathlib leaves. The original statement, statement dependency, chapter, unit, creation record, and blueprint ancestry are preserved. The new endpoint-evaluation node is an auxiliary generic input, strictly smaller than the item, and the item cites it in Step 2. No unit realization record is needed: this is an auxiliary descendant, not the unit's key node.

## Attachments

None. Searching `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the full item id, path-space/mapping-path/homotopy-fiber phrases and `SSet.Path` found no declaration of this item. The broader Kan search returned Kan extension declarations in ordinary category theory, which do not concern Kan complexes. No upstream-master sorry declaration is being treated as a finished proof.

## Wanted sources

WANTED: an archived copy of Kerodon Example 3.1.8.10 (0101), Corollary 3.1.3.3 (00TM), Remark 3.4.0.6 (0328), Definition 3.1.7.12 (00UA), and Corollary 3.6.4.3 (03X7), for lem-coef-space-path-fibration-replacement. I read the currently available online texts of 0101, 00TM, 0328 and 03X7. The literal meaning of 00UA is also exposed by the existing realization-testing node; the final source check follows its link. No matching Stacks tag was found: these are Kerodon tags and must not be relabelled as Stacks tags. Nothing was downloaded to the read-only literature tree.

The proof is marked `proof_origin.by = agent`, with the blueprint ancestry as its local document: the online path-fibration route is expanded by an explicit simplicial contraction and horn fillers, rather than pretending to follow an archived text that is not present.

## Audit of the input and searches

The item is true as imported. Its inline Kan-fibration convention correctly includes both outer horns and imposes no dimension-zero surjectivity condition. Its homotopy-fiber formula uses evaluation at 0 to attach to P and evaluation at 1 to fix q; those orientations are retained. No STATEMENT-DISPUTED correction is needed.

I read the chapter record `sec-six-functors`, unit `sk-prop-sf-biduality-general`, and the current ancestor proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. The ancestor's second paragraph is the derived mapping-complex/finite-coefficient adjunction computation. This item supplies a foundational tool below its recorded enhancement ancestry; it changes neither that computation nor the unit route. No forbidden SGA source was used.

The imported Mathlib search record included an invalid Loogle expression (`SSet PathObject fibration homotopy fiber`), so I did not use it as evidence of absence. I preserved that inherited record and appended fresh logged searches, all actually run through msearch.py under Q14 and this item:

- LeanFinder: “For a map of Kan complexes the mapping path space gives a Kan fibration replacement with a weak homotopy equivalence constant path inclusion”.
- LeanFinder, second phrasing: “Pullback of the simplicial path object along a map gives a fibration replacement and constant paths are a homotopy equivalence”.
- Loogle: `SSet.Path`.
- grep: `PathObject|path.?fibration|homotopyFiber|homotopy.fiber`, under `AlgebraicTopology`.
- LeanSearch: “Mapping path space factorization of a map of Kan complexes into a weak equivalence followed by a fibration”.

All five completed successfully. I read `Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean`, including the PathObject structure, weakEquivalence_ι field, IsGood condition and projection instances, and `Mathlib/AlgebraicTopology/SimplicialSet/Path.lean`. Abstract PathObject data assume the weak-equivalence property which this item must establish, and do not construct Fun(Δ¹,Q) or connect it to the geometric-realization convention. SSet.Path is a finite sequence of edges. Neither is an exact match or a one-line specialization of this item. The reported trans/trans_P hits concern gluing two already supplied abstract path objects, not this replacement.

Whole-DAG searches for path spaces, Kan fibrations, homotopy fibers and anodyne pushout products, and whole-blueprint searches `path`, `Kan`, and `00TM`, found the existing generic tools used here and no duplicate imported statement of the item. I opened the candidate Kan-pullback-path comparison, homotopy-pullback invariance, isofibration exponentiation and Kan mapping-space invariance statements. They are different comparison theorems, not the endpoint restriction theorem as stated here. There was therefore no reason to create another endpoint-fibration node or a one-clause replacement of the item.

## Not duplicates

`lem-coef-space-endpoint-evaluation-fibration` vs `lem-coef-kan-pullback-path-comparison`: the new node states only the endpoint restriction Kan-fibration input for one Kan complex, whereas the existing node states the full two-map path pullback Kan-complex and constant-path weak-equivalence comparison; the endpoint fact occurs only as an intermediate proof step there.

The endpoint-evaluation node is a generic mapping-space input, not a restatement of the item: it has no map $f:P\to Q$, no pullback $E_f$, no constant-path weak equivalence, and no homotopy-fiber conclusion. The realization comparison reuses `lem-cbc-realization-weak-equivalence`; the contraction and strict-fiber equality remain elementary calculations in the item.

## Review by Q14

I checked the item against Kerodon 0101 and 0328. Example 0101 constructs the same pullback, with the same endpoint evaluations and constant-path map. Its second bullet proves the projection is a fibration by endpoint restriction and the Kan condition on P. I wrote those liftings explicitly. Its first bullet proves the constant-path map is a weak equivalence through a trivial fibration; the draft instead supplies its actual simplicial deformation retraction and applies the already existing weak-equivalence testing theorem. That change is below the unit route and preserves every clause and every hypothesis.

Step 1 uses the statement of `def-cbc-enhanced-diagrams-cones`: its internal Fun, degreewise pullbacks, evaluation and constant maps give exactly the displayed simplex formulas. Checking the two endpoints gives ri = id and pi = f; there is no existence theorem hidden here.

Step 2 uses the statement of the new endpoint-evaluation node. I opened its Kerodon 00TM source and checked that its endpoint order is exactly $(0,1)$ and that it includes all horns, including outer horns. The item uses only the node's stated right lifting property: a horn of paths and prescribed endpoint simplices form the lifting square, and the extension has the required endpoints. This removes the prior dependency on `lem-coef-sset-anodyne-pushout-product`, whose Mathlib-node statement depended on the Kan-Quillen node and created a cycle through the existing homotopy-fiber-detection node. The new node is strictly smaller than the item and does not cite that cyclic chain.

Step 3 uses only the definition node and Step 2 already proved. P Kan fills the P-coordinate of the horn first; endpoint restriction fills its path-coordinate with the prescribed pair (fx,b). The two fillings have identical horn restrictions, so the pair lies in E_f. To see E_f is Kan, Q Kan supplies b before the same lifting. Thus the proof does not assume E_f or Fun(Δ¹,Q) Kan in advance. Pullback and composition stability are proved by the two successive lifts, not quoted without nodes.

Step 4 is elementary from the degreewise Fun and product definitions. I checked that pointwise minimum of monotone [n] → [1] maps is monotone and commutes with restriction, that min(0,t) = 0 preserves the pullback condition, and that min(s,0) = 0 and min(s,1) = s give exactly ir and id. This homotopy is on E_f, not in the slice over Q: no false assertion that it fixes the endpoint at 1 is made. The n-simplex formula allows t to vary with z, so it really defines a simplicial map and not just a deformation on vertices.

Step 5 uses `lem-cbc-realization-weak-equivalence`, whose statement I opened in full. It gives an if-and-only-if for all simplicial maps between small simplicial sets, using the exact geometric-realization homotopy-group convention and edge components of the specified internal Fun. It does not require source or target Kan. I checked the online 03X7 comparison supporting that statement. For any Kan W, the two precomposition maps preserve edges by restriction. The equality ri = id gives one inverse identity, and the edge aH identifies the other composite on every vertex class. No assertion about abstract model homotopies or about realization preserving an arbitrary product is needed. The criterion therefore applies directly to i. Because this is a generic tool of the smooth-purity unit, I declared the cross-unit use in `split_report.tool_uses`: it is not a replacement of any geometric biduality step. Traversing the current statement and proof dependencies of both cited theorems found no path back to the item.

Step 6 uses the actual homotopy-fiber formula in the definition node, not a generic pullback-definition citation that lacks it. Taking the strict fiber imposes exactly γ(1,z) = q, with γ(0,z) = fx inherited from E_f, degree by degree. The operators are also identical. The Kan assertion follows by the horn lift for p with constant prescribed base simplex. This is a literal equality of the prescribed models, so no unrecorded invariance or homotopy-pullback comparison is used.

I checked sections B–E against these files. There are no new statement-only nodes to validate or pair against same-tag existing nodes. All proof dependencies are the union of the step citations, with a verbatim extract for each pair in citations.json. The only new node is the endpoint-evaluation statement; its three Mathlib searches are recorded in the node and searches.jsonl. Every non-elementary input is a cited statement (pushout-product in Step 2, realization criterion in Step 5); elementary steps write their constructions and verifications. The text never takes a construction from the proof of another node. The only off-unit proof tool is declared explicitly. Smallness is preserved by finite products, pullbacks and the internal Fun construction in the fixed universe.

Edge cases: P = Q = ∅ gives E_f = ∅, the identity inclusion, a vacuously Kan map, and no vertices q. P = ∅ with Q nonempty again gives E_f = ∅, i an identity and empty strict/homotopy fibers; none of the proof forces these fibers to be inhabited. If Q = ∅ a map f forces P = ∅. For P = Q = Δ⁰ all maps are identities. For f = id_Q the path object is Fun(Δ¹,Q), and the same minimum contraction retracts to constant paths while allowing the final endpoint to vary. A base vertex in a component missed by f gives an empty fiber, consistently with the statement. A nontrivial loop space can occur in a fiber; the proof never claims the fibers themselves are contractible. All outer horns, including n = 1, were retained in the lifting argument.

The corrections during this review were expository: I avoided the inherited invalid Loogle pattern, replaced a possible appeal to abstract model weak equivalences by the existing geometric-realization testing statement, and gave the n-simplex contraction formula so compatibility with simplicial operators is verifiable. No source or statement error was found.

## Unfinished work and validation

Nothing mathematical remains for this one-level split. The cited realization criterion remains its own existing unsplit item, as the stage-1 contract permits. This delivery does not claim that the entire branch is formalized.

The required dry run is recorded below after it completes. No push is authorized for this worker; the second reader delivers.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against Kerodon Example 3.1.8.10 (0101) and Remark 3.4.0.6 (0328), including endpoint orientation, outer horns, empty spaces, and empty fibers; PASS.
- Step 1: checked the degreewise pullback, endpoint maps, constant paths, and identities against 0101 and `def-cbc-enhanced-diagrams-cones`; PASS.
- Step 2: checked the horn lifting square and endpoint orientation against Kerodon Corollary 3.1.3.3 (00TM) and the new endpoint-evaluation node; PASS.
- Step 3: checked the two successive horn lifts and the Kan conclusion using Step 2 and the Kan definition; PASS.
- Step 4: checked pointwise minimum on monotone simplices and both homotopy endpoints against the path-object construction in 0101; PASS.
- Step 5: opened Kerodon Definition 3.1.7.12 (00UA) and Corollary 3.6.4.3 (03X7); together they give exactly the criterion in `lem-cbc-realization-weak-equivalence`. The edge aH and ri = id give the two inverse component maps; PASS.
- Step 6: checked strict fiber equality and its horn lifting against the homotopy-fiber definition in `def-cbc-enhanced-diagrams-cones` and 0328; PASS.
- New node: endpoint evaluation, checked as a strict auxiliary input; its 00TM overlap with `lem-coef-kan-pullback-path-comparison` is documented under `## Not duplicates`, and its Mathlib searches are recorded.

Changes made: added this independent second reading and verified the previously indirect source check at 00UA. Its Kan-target definition and 03X7 together validate the original Step 5. Repaired the preflight cycle by replacing the cyclic Mathlib pushout-product citation in Step 2 with the new standalone endpoint-evaluation auxiliary node; the item statement is unchanged. Step 3 legitimately uses the already proved Step 2 and requires no extra external citation. Tested empty P or Q, the point, identity maps, missed components, and all one-dimensional outer horns. No forbidden SGA source is used.

Independent Mathlib search: I ran LeanFinder through msearch.py with the query “In simplicial sets, the pullback of the exponential by the interval along evaluation at zero factors any map between fibrant objects through a trivial cofibration and a fibration”. The eight returned hits concern abstract PathObject composition/projections and FibrantBrownFactorization; none constructs the specified internal exponential or identifies geometric-realization weak equivalences. The actual result is in searches.jsonl. The existing proof therefore remains split, rather than a Mathlib leaf.

Validation: the required server dry run printed `OK (not pushed) deliver/Q14/lem-coef-space-path-fibration-replacement at 6fe75eebfe: preflight passed` during review. The final dry run of the retained original proof and completed second reading printed `OK (not pushed) deliver/Q14/lem-coef-space-path-fibration-replacement at d04f50f628: preflight passed`. All eight citation records were also checked verbatim against the current cited statements, and the 71-node dependency closure is acyclic.

Final validation after the cycle repair: `deliver.py Q14 lem-coef-space-path-fibration-replacement --no-push .` printed `OK (not pushed) deliver/Q14/lem-coef-space-path-fibration-replacement at 6cbed68f1a: preflight passed`. The mandated server check `srvcheck.py weil-newtargets Q14 lem-coef-space-path-fibration-replacement check_dag` then printed `check_dag OK: no finding introduced by the sandbox or on its nodes`. The first preflight's six-node cycle was thereby eliminated.


## Second reading by Q14

This independent reading supersedes the earlier round's search conclusions and node counts. The delivered split has **one new node, which is a Mathlib leaf**, and no new unsplit nodes. The item's statement is unchanged. The original worker's sections above are retained as requested.

- Item statement: checked hypothesis by hypothesis against online Kerodon Example 3.1.8.10 (0101), Remark 3.4.0.6 (0328), and the current definition node; PASS. The endpoint order, positive-dimensional outer horns, geometric-realization convention, and strict-fiber formula agree.
- Step 1: checked against 0101 and the actual internal-Fun, degreewise pullback, evaluation and constant-map statements in def-cbc-enhanced-diagrams-cones; PASS. The formulas give ri = id and pi = f and commute with every restriction.
- Step 2: checked the auxiliary statement against Kerodon Corollary 3.1.3.3 (00TM) and Mathlib PushoutProduct.lean:144-147; PASS after repairing a tab-corrupted TeX arrow and recognizing the auxiliary as a Mathlib leaf. The displayed union is precisely the horn of paths with its two prescribed endpoint simplices; no unrecorded pushout-product theorem is used.
- Step 3: checked against the all-horn Kan definition and the endpoint lifting proved in Step 2; PASS. Fill the P-coordinate, then the path-coordinate with endpoints (fx,b); to fill a horn of E_f first fill its projected Q-horn. The argument uses only the stated Kan hypotheses and does not assume the desired conclusion.
- Step 4: checked the explicit minimum formula against the internal-Fun operators and the standard-simplex definition; PASS. Minimum is monotone in the product order, commutes with precomposition, fixes the initial endpoint, and has the stated endpoints ir and id. No assertion that it fixes the final endpoint is needed.
- Step 5: opened and read the entire statement of lem-cbc-realization-weak-equivalence and checked it against Kerodon Definition 3.1.7.12 (00UA) and Corollary 3.6.4.3 (03X7); PASS. Precomposition preserves edges, ri = id gives one inverse identity, and aH gives the other on every edge component. The cited criterion has no additional Kan, injectivity or nonemptiness hypothesis. This is a generic tool from sk-prop-sf-cbc; no statement in the item's unit supplies that realization comparison, and no geometric unit route is replaced. The existing split_report.tool_uses explains this use for the maintainer; no maintainer-owned tool_uses was added.
- Step 6: checked against the precise homotopy-fiber formula in def-cbc-enhanced-diagrams-cones and 0328; PASS. The strict fiber has exactly those simplices and operators, and its horns lift against p over the constant simplex at q.
- New node lem-coef-space-endpoint-evaluation-fibration: checked against the general restriction theorem at 00TM, the existing same-tag lem-coef-kan-pullback-path-comparison, lem-coef-infinity-isofibration-exponentiation, and Mathlib SSet.instFibrationAppPreOfMonoOfKanComplex; PASS as a Mathlib leaf, replacing the previous unsplit status. Read PushoutProduct.lean:144-147, CategoryWithFibrations.lean:44-54,71-100, KanComplex.lean:36-48, and the existing compiled .ilean declaration index (no compiler run). Restricting a map from the two constant-vertex copies of Δ[n] gives the canonical degreewise target isomorphism Fun(∂Δ[1],Q) ≅ Q × Q, with inverse defined on each copy. Under it, the instance specializes directly to endpoint evaluation. Its statement is self-contained, cites its definition node, contains no proof, and now has valid TeX.

Small cases checked independently: empty P or Q (a map to empty Q forces empty P), P = Q = Δ⁰, identity maps, and a discrete Q with vertices in different components. The endpoint map need not be surjective onto pairs in different components: no compatible horn lifting square forces such a path. For n = 1 both horns are included, and the two successive lifts remain valid. For n = 0 the theorem requires no horn filling and no nonemptiness. Empty fibers and noncontractible loop fibers are allowed. No false or missing hypothesis was found; no STATEMENT-DISPUTED repair is needed.

Duplicate and ancestry checks: searched all DAG statements for endpoint/evaluation/restriction fibrations, opened the two closest nodes named above, and reran whole-blueprint searches for Kan, path and 00TM. None of the imported blueprint nodes states this result. The existing path-pullback comparison states the Kan property of a two-map homotopy pullback and a comparison weak equivalence; it does not state endpoint restriction is a fibration. The isofibration node's final clause concerns fixed-endpoint fibers, not the endpoint map into Q × Q. Read the chapter, unit, and current main-20261015 ancestor proof paragraph 2 and confirmed the recorded ancestry with blueprint_refs.py ancestor. No blueprint_update overrides this item. No SGA source was used. Searches in the read-only slopmaster2 source by the item id, endpoint id, path-fibration terms and restriction-instance vocabulary found no project declaration to attach. Upstream-master sorry declarations were not used as finished proofs.

Changes and reasons:

1. Converted the sole new auxiliary to status mathlib and recorded SSet.instFibrationAppPreOfMonoOfKanComplex, its actual file, line 144, lines 144-147 read, and the explicit endpoint specialization. This avoids creating an unnecessary unsplit item. The independently phrased LeanFinder, grep, LeanSearch and valid Loogle queries all ran through msearch.py; their actual search-log records are copied into the node. Loogle's query `"SSet.instFibration"` returns the exact named instance. The broader semantic searches returned category/fibration infrastructure, so the source inspection and valid Loogle result determine the match.
2. Replaced the tab characters accidentally produced by JSON escapes in the auxiliary's Q × Q expression and Step 2's arrow with single TeX backslashes. Updated the endpoint citation quote to remain verbatim.
3. Corrected Step 2's stale pushout-product source description, the split summary's stale zero-node count, and the inherited invalid Loogle query's verdict. Its original parser error remains recorded; it is not evidence of absence.
4. Retained the six correct proof arguments, the item statement, statement dependencies, source intent, unit/chapter, and ancestry. Checked all eight citation records against the actual cited statements; they are verbatim and exhaust the step citations.

Validation: the required server dry run and final delivery are performed after this report is appended. No Lean, Lake, compiler, local preflight, local review_split.py, or local check_dag.py is run.

Second-reader validation result: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q14 lem-coef-space-path-fibration-replacement --no-push .` printed `OK (not pushed) deliver/Q14/lem-coef-space-path-fibration-replacement at 03ab6ba3bc: preflight passed`. The required server preflight passed. An additional read-only traversal of the repaired item's seven-node dependency closure found no missing references or cycles. Final delivery is authorized by the second-reader brief.
