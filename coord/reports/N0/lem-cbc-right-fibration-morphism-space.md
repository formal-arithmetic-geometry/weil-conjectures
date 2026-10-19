# Stage-1 report: lem-cbc-right-fibration-morphism-space

Files written:

- `dag/nodes/sec-smooth-purity/lem-cbc-right-fibration-cartesian-lifts.json` — statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-cbc-right-fibration-cartesian-mapping-fiber.json` — statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-cbc-right-fibration-morphism-space.json` — split item; no Mathlib match.
- `citations.json` — verbatim citations for all three proof steps.

Attachments: none. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` found no declaration tagged `(blueprint: lem-cbc-right-fibration-morphism-space)` and no declaration stating this theorem. The item therefore required a split.

WANTED: Kerodon Proposition 5.1.2.1 (tag 01TL), Proposition 5.1.4.15 and Remark 5.1.3.8, for `lem-cbc-right-fibration-cartesian-lifts` and `lem-cbc-right-fibration-cartesian-mapping-fiber`; these sources are online references rather than archived files under `literature/`.

The imported item was unsplit and had only the enhanced-diagram definition as a statement dependency. I retained its statement and its right-pinched/homotopy-fiber conventions. The two new nodes do not duplicate `lem-coef-infinity-right-fibration-fibers` (that node proves Kan fibers and invariance under equivalences, with no cartesian-lift or mapping-fiber formula), `lem-coef-infinity-arrow-target-right-fibration` (fixed-target arrow projection only), or `lem-coef-infinity-slice-right-fibration` (join-slice projection and mapping-space fibers). No blueprint node states either new lemma.

## Not duplicates

Second-reader additions (the source-tag duplicate gate reports these pairs):

`lem-cbc-right-fibration-space-fiber` vs `lem-coef-spaces-homotopy-fiber-detection`: the new lemma upgrades a right fibration over a Kan base to an all-horn fibration and identifies its strict fiber with its homotopy fiber. The existing statement compares homotopy fibers of two maps along a square of Kan spaces; it contains no all-horn conclusion and no strict-fiber comparison. Both cite Kerodon Section 0106 for different results.

`lem-cbc-right-fibration-space-fiber` vs `lem-weil-pbc-abelian-short-exact-kernel`: the latter states that the injection in a short exact sequence in an abelian category is a kernel. Its source is Stacks Homology Definition 0106, unrelated to Kerodon Section 0106; it says nothing about simplicial fibrations or homotopy fibers. I opened both the statement and source record.


`lem-cbc-right-fibration-cartesian-lifts` vs `lem-cbc-right-fibration-morphism-space`: the new node isolates existence and contractibility of cartesian lift choices, while the item additionally asserts the mapping-space/homotopy-fiber equivalence and pullback compatibility.

`lem-cbc-right-fibration-cartesian-mapping-fiber` vs `lem-cbc-right-fibration-morphism-space`: the new node only identifies one strict mapping-space fiber over a fixed edge, while the item assembles all edges into the global homotopy-fiber equivalence and transport map.

`lem-cbc-right-fibration-cartesian-lifts` vs `lem-coef-infinity-right-fibration-fibers`: the former gives existence and contractibility of cartesian lifts with fixed target; the latter gives Kan-ness of strict fibers and fiber invariance under an equivalence.

`lem-cbc-right-fibration-cartesian-lifts` vs `lem-coef-infinity-arrow-target-right-fibration`: the former is the general cartesian-lift/uniqueness theorem for any right fibration; the latter only proves that one particular fixed-target arrow projection is a right fibration.

`lem-cbc-right-fibration-cartesian-mapping-fiber` vs `lem-coef-infinity-right-fibration-fibers`: the former identifies each mapping-space fiber over a base edge with a path space in a source fiber; the latter does not discuss mapping spaces or cartesian edges.

`lem-cbc-right-fibration-cartesian-mapping-fiber` vs `lem-coef-infinity-slice-right-fibration`: the former is the cartesian mapping-square calculation for arbitrary right fibrations; the latter identifies fibers of a specific join-slice projection with right-pinched mapping spaces.

## Review by N0

I read the imported item, the `sk-prop-sf-cbc` unit, the smooth-purity chapter record, and the enhanced-diagram definition. I also read the existing right-fibration nodes cited in the duplicate audit and checked the Lean source trees for an exact declaration or blueprint tag. The source for both new foundations is Kerodon 01TL: Propositions 5.1.2.1 and 5.1.4.15 and Remark 5.1.3.8. The Mathlib searches were run through `msearch.py` for each new node with leanfinder, loogle, grep, and leansearch; hits were ordinary fibered-category or model-category declarations and did not state either higher-categorical result.

Step 1 uses the exact cartesian-lift statement: the right-fibration horn condition gives a lift over every edge, and the cited node says the space of such lifts with fixed target is contractible and that the source lies in the source fiber. I checked the endpoint hypotheses $a:x\\to y$ and $e'\\in E_y$, including the identity-edge case.

Step 2 uses the exact mapping-fiber sentence of the second new node. Its hypotheses provide $e\\in E_x$, $e'\\in E_y$, and a chosen cartesian lift over $a$; the conclusion is precisely the strict fiber/path-space comparison needed for the transport map. The contractibility from step 1 supplies coherent dependence on $a$.

Step 3 cites the verbatim homotopy-fiber definition from `def-cbc-enhanced-diagrams-cones`. It checks that the definition uses a path from $t_{e'}(a)$ to $e$, while step 2 gives the reverse path orientation, and invokes the canonical path-reversal equivalence in the Kan fiber. This yields the claimed natural equivalence and preserves pullback naturality. I corrected the originally absent proof, filled the item blueprint place, added the two necessary statement-only foundations, and recorded all citations verbatim.

Nothing was compiled or written in the live project, in accordance with the stage-1 restriction.


## Second reading by N0

I am the independent second reader, not the split's author. I opened the item, both proposed new nodes, every statement cited in the repaired proof, the unit and chapter records, and the current main-20261015 blueprint theorem and proof. The unchanged item has quasicategories E and B, a right fibration with the positive-index horn convention, specified vertices in the strict fibers, right-pinched mapping spaces, and homotopy fibers directed from the image to the specified point. The online sources are Kerodon, not Stacks; identically numbered Stacks tags are unrelated. I read Kerodon 01TL (Proposition 5.1.2.1), 01U5 (Remark 5.1.3.8), 01UM (Proposition 5.1.4.15), 0154 (Proposition 4.2.5.4), 01KQ (Proposition 4.6.4.13), 01L5 (Proposition 4.6.5.10), 01NV (Corollary 4.4.3.8), and Section 0106, Proposition 3.4.0.7. The item is the same generic right-fibration formula; its source now identifies the explicit exponentiation proof rather than claiming that 01TL alone supplies it.

- Original step 1: checked against 01UM and 01U5 and the proposed lift node; existence is correct, but the undefined “simplicial space of cartesian edges” and the claim that its pointwise contractibility supplies all coherence needed replacement by an explicit lift space.
- Original step 2: checked against 01TL and the proposed mapping-fiber node; a cartesian homotopy-pullback square does not, without further fibration/comparison arguments, give the stated strict-fiber formula and its assembled family. Replaced the step and removed the node.
- Original step 3: checked against the exact path model in def-cbc-enhanced-diagrams-cones; passing from individual fibers to total spaces was not elementary, and canonical simplicial path reversal was not supplied by that definition. Replaced it by cited natural maps between homotopy fibers.

- Repaired step 1: checked the entire statements of def-cbc-enhanced-diagrams-cones, lem-coef-infinity-pinch-comparison (01L5), and lem-coef-infinity-right-fibration-fibers; these give the precise mapping model and Kan spaces A and E_x. The displayed degreewise definitions introduce L, r and s without additional claims. PASS.
- Repaired step 2: checked lem-coef-infinity-right-fibration-exponentiation against 0154 with the correctly oriented final-vertex horn Lambda_1^1={1}; its conclusion is exactly the trivial Kan fibration pulled back to r. Checked the existing Mathlib leaf lem-weil-pbc-trivial-kan-lifts-monomorphisms against SSet.rlp_monomorphisms, CategoryWithFibrations.lean:127-132, and I at line 38. Its lifting statement gives horn fillers over the Kan base A; lem-cbc-kan-fibration-fiber-criterion then applies with all its Kan-fibration hypotheses established. PASS.
- Repaired step 3: checked the Mathlib leaf's statement with the injections empty-to-A and A times boundary-to-A times simplex. The section space and its simplicial operators are restriction in the simplex parameter, so every boundary, including dimension zero, lifts. The cited Kan/trivial-fibration criterion gives contractibility; a section defines one map on the whole A. PASS.
- Repaired step 4: checked the degreewise equality L=E_x times_E E_arr(e') and the exact arrow-target statement (01KQ). Pullback horn lifting gives the required right fibration s. The new space-fiber lemma has a Kan base, no surjectivity assumption, and gives exactly the constant-path map from its strict fiber U_E(e,e') to its homotopy fiber. PASS.
- Repaired step 5: read lem-coef-spaces-homotopy-fiber-detection in full: apply its forward direction to sigma over the identity of E_x and then to j_B over that same identity. All four total spaces and bases are Kan; sigma is a weak equivalence because r sigma is the identity and r is a weak equivalence. Read the natural pinch statement for the last comparison. Every homotopy-fiber path has the orientation in the definition. PASS.
- Repaired step 6: checked the explicit coordinate identifications under B' to B, the induced section formula, and the parameterized construction over A times E_y. The previously cited exponentiation theorem supplies the latter trivial Kan fibration. Boundary lifting supplies all higher comparisons of sections, while the cited pinch and constant-path maps are natural and the fiber-detection node describes the induced fiber maps explicitly. PASS.

- Removed node lem-cbc-right-fibration-cartesian-lifts: read against 01UM and 01U5 and the existing exponentiation node. Existence is a horn lift, and full coherent contractibility follows by applying the already existing exponentiation statement to the final-vertex horn. The proposed node therefore adds no necessary foundation. Removed before publication (B3, C5, D1).
- Removed node lem-cbc-right-fibration-cartesian-mapping-fiber: read against 01TL. It asserted the central local calculation of the item without defining its cartesian notion or justifying the strict/homotopy comparison. The direct arrow-space calculation in repaired steps 4-5 proves what the item needs and avoids this proposed clause-node. Removed before publication (B3, C3, D1).
- New node lem-cbc-right-fibration-space-fiber: compared hypothesis by hypothesis to 01NV, (3) implies (1), and Proposition 3.4.0.7 in 0106, specialized to the vertex inclusion. It has arbitrary small X, a Kan base S, positive-index horn lifting, all-horn conclusion, Kan total space, and the explicitly defined constant-path comparison with the correct orientation. Its statement contains no proof; every notion is inline or comes from def-cbc-enhanced-diagrams-cones. TeX is encoded once. This is a generic fibration theorem, not a mapping-space or transport formula. PASS B1-B7.

The new lemma was tested on empty X, empty S (forcing X empty), a discrete Kan base, the identity of a Kan complex, and a Kan complex mapping to a point. The Kan-base assumption is essential: the inclusion of vertex 0 into Delta^1 is a right fibration but cannot lift the initial dimension-one horn over 0-to-1. For the item I also checked E=S times B with S discrete (both sides are empty for unequal fiber points and give Map_B(x,y) for equal points), B a point and E a groupoid nerve (the formula recovers its path spaces, including nontrivial loops), and empty A (L empty, with a unique section). The section argument includes n=0 for existence and n=1 for compatible choices; it imposes no unwanted nonemptiness condition on a fiber.

Duplicate audit: searched all DAG source tags and statements, and ran blueprint_refs.py ancestor plus searches for “right fibration”, “Kan fibration”, “homotopy fiber” and “boundary lifting” over the whole imported blueprint; all four searches returned zero blueprint matches. The ancestor is thm-cbc-finite-level-proetale, and the exact current source is its opening compactification-choice sentence; the current blueprint does not state this extra foundation. Compared the new lemma with lem-coef-infinity-right-fibration-fibers (only Kan fibers and invariance under categorical equivalences), lem-coef-right-fibration-contractible-fibers (requires every fiber contractible, with arbitrary base), and lem-cbc-kan-fibration-fiber-criterion (already assumes all-horn lifting and does not identify strict with homotopy fibers). None states the new lemma. The raw 01NV text hits lem-pc-perfect-generation-koszul-orthogonal and lem-weil-pbc-integral-algebra-directed-colimit-finite were opened: both are unrelated scheme-theoretic statements, and neither source is the Kerodon corollary.

Independent Mathlib searches, with different and more general wording than the first reader, were run through msearch.py; the unmodified actual results are in searches.jsonl. The new node records both semantic phrasings, LeanSearch, Loogle and source grep exactly as logged. The Loogle candidate SSet.instFibrationAppPreOfMonoOfKanComplex was read at AnodyneExtensions/PushoutProduct.lean:144-147: it proves internal-Hom restriction into a Kan complex is a fibration and does not upgrade an arbitrary right fibration. The boundary-lifting search found SSet.rlp_monomorphisms, but its existing leaf was reused, so no duplicate Mathlib node was created. Searches of both read-only Lean source trees and dag/lean_names_upstream.json found no exact theorem or relevant blueprint attachment.

Changes and reasons:

1. Kept the item's statement byte-for-byte; wrote a six-step proof with an explicit coherent lift space instead of unsupported pointwise assembly and path reversal.
2. Removed both unpublished proposed nodes; added one smaller statement-only general space-fiber foundation, with log-backed independent searches.
3. Reused the existing exponentiation, fiber-Kan, arrow-target, pinch, boundary-lifting and homotopy-fiber-detection statements. The general model-structure node lem-coef-kan-quillen-right-proper was considered and rejected: its statement dependency leads through lem-cbc-enhanced-functor-cone-calculus back to this item. Every final dependency was checked to have no path back to the item.
4. Replaced citations.json with one verbatim full statement for every citation of every repaired step; the original first-worker report and its Review by N0 section remain above as requested.
5. Declared the five generic coefficient-foundation statements as tool uses in split_report with their mathematical purpose. They do not change the compact-support route; the current unit has no right-fibration/model-comparison theorem of its own. The Mathlib boundary-lifting leaf is already an admissible tool.

WANTED archival references for the maintainer: online Kerodon 0154, 01KQ, 01L5, 01NV and Section 0106, Proposition 3.4.0.7. No source copy was written to the shared repository. All edits are confined to this sandbox. No Lean file, compiler, Lake/build tool, live-project file, launcher file, or shared-repository git command was used.

Dry-run repair: the first packaging attempt requested the preceding two explicit source-tag duplicate comparisons. Added them after opening both node statements; no mathematical change was required.

Validation: deliver.py --no-push printed OK after the duplicate-report repair; the final notes correct the internal-Hom candidate reference to PushoutProduct.lean:144-147, verified from the numbered source. The required server checks are repeated on these final contents before delivery.

Final E5 correction: step 6 now displays the injections A-prime times boundary into A-prime times simplex (also with an arbitrary K parameter), the universal pullback over A times E_y, and its section-boundary extension. This replaces the two references to “the same” extension argument. The cited statements and citations.json remain exactly the ones read above.
