# Stage-1 report: lem-coef-kan-weak-equivalence-space-edge

## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-weak-equivalence-space-edge.json`: statement, split in three steps; no Mathlib match for the complete coherent-nerve assertion.
- `citations.json`: seven verbatim statement quotations, covering every step/dependency pair.
- `report.md`: this report. Retained `searches.jsonl` and the previous split and ancestry; appended one targeted candidate-location search and the previously logged Q114 searches to the node.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and coherent-nerve/weak-equivalence terminology found no declaration stating this item. Upstream master is not treated as finished proof evidence.

## Sources wanted

WANTED: archived Kerodon, Tags 00UB (Proposition 3.1.7.13), 03X7 (Corollary 3.6.4.3), 03PJ (Proposition 3.1.7.17), 06QR (Example 4.6.7.7) and 01PF (Subsection 4.6.8), for lem-coef-kan-weak-equivalence-space-edge. Read online; these are Kerodon identifiers, not Stacks tags. No archived Kerodon file was found in literature/. The construction is explicitly marked agent-written. No unavailable source was downloaded into the shared repository.

## Corrections and scope

The saved sandbox already had a split and citations but no report, so the condition requiring a dry run before any repair did not apply. Compared it with the current repository: the mathematical statement, source, ancestry, creation data, chapter and unit agree; the repository item is still unsplit. Preserved the saved argument, inherited search records, and existing citation quotations. Expanded the generic phrase about reversing an edge into its exact outer horn. Expanded the triangle assertion into the enriched functor, composition check and face restrictions. Added the definition citation wherever its internal-Hom or equivalence-edge clause is used. No statement dispute, no changed hypotheses and no new nodes.

The node's inherited source references 06QR and 01PF as background. 06QR provides a mapping-space homotopy equivalence, not an isomorphism or this precise inverse-triangle theorem. This split does not use that comparison to identify different mapping-space models: it constructs the triangles directly in the subset-poset nerve. The current main-20261015 ancestor is at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md`; the stored ancestry is historical and remains untouched. This item supplies the technical space-equivalence input below the specified coherent mapping-adjunction route, without replacing a unit step or altering a chapter.

## Not duplicates

No new nodes. The existing Whitehead inverse and Kan mapping-homotopy-invariance statements supply the non-elementary inputs; reverse-edge horn filling and the enriched two-simplex are short direct arguments and were not made into nodes. Whole-blueprint searches for `Kan` and `coherent nerve`, and DAG searches for coherent nerves/inverse triangles/06QR, found no imported blueprint node giving an exact alternative attachment for this item.

## Mathlib searches

Read the retained Q114 searches.jsonl entries from 11:38 and 11:57 UTC. These contain successful LeanFinder (two phrasings), Loogle, grep and LeanSearch searches. In particular the Q114 LeanSearch succeeded; it is separate from the inherited Q106 unavailable record, which is retained unchanged. The logged hits are ordinary nerve equivalences, homotopy-category infrastructure and model-category homotopy facts. Recorded their actual query texts and outputs in mathlib_searches, without rerunning unchanged questions.

The additional grep located candidate declarations so their types could be checked. Read `Mathlib/AlgebraicTopology/SimplicialSet/HomotopyCat.lean:96-118`: `SSet.OneTruncation₂.nerveHomEquiv` concerns an ordinary category's nerve. Read `Mathlib/AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean:70-90`: `weakEquivalence_toHoCat_map_iff` compares weak equivalences with a homotopy quotient; it does not supply coherent-nerve triangles. Read `Mathlib/AlgebraicTopology/SimplicialNerve.lean:14-37,53-135,188-208`: the subset-poset coherent nerve is defined, but neither this Kan-complex edge theorem nor a one-line specialization is stated; even the general locally Kan quasicategory theorem is listed as a project. Thus this item remains a split, not a Mathlib leaf.

## Review by Q114

I read the current item's statement, its historical blueprint ancestor, the chapter and unit records, and the main-20261015 ancestor. I read Kerodon 06QR and 01PF in the browser, and 00UB and 03PJ directly online after the browser fetches timed out; 03X7 was readable in the browser. 00UB states Whitehead's converse for Kan complexes, and 03X7 reconciles its weak-equivalence convention with geometric realization. 03PJ uses the Kan internal-Hom fact in its proof (with a reference to 00TN). The item is an agent construction from the explicit definitions and existing DAG statements, not a claim that 06QR alone proves it. There are no new-node sources to review.

For step 1 I opened `lem-cbc-kan-whitehead-inverse` and checked its full statement: it gives an actual simplicial g and actual maps H,J with the stated endpoint equations, under precisely the Kan and realization hypotheses here, including empty and disconnected objects. I also opened `def-cbc-enhanced-diagrams-cones`: its internal-Hom degree-one formula identifies these homotopies with edges. No passage from a homotopy class to a chosen actual map is left implicit.

For step 2 I opened `lem-cbc-kan-mapping-homotopy-invariance`: its statement explicitly asserts that both internal functor simplicial sets are Kan, not just that precomposition is a weak equivalence. Identity maps meet its realization hypothesis; choose Z=A and Z=B respectively. I checked the definition of the outer horn in `def-cbc-enhanced-diagrams-cones`. Lambda^2_0 consists of edges 01 and 02, so prescribing h:x->y and the identity x->x leaves exactly the missing edge 12:y->x. This constructs the required reversal without pretending that a simplicial interval admits an order-reversing simplicial automorphism. The reverse edge's endpoints are all step 3 needs.

For step 3 I opened `def-coef-infinity-category-of-spaces` in full, including its explicit subset posets and union composition, and `def-coef-coherent-nerve-infrastructure`, which specifies postcomposition on enriched functors. For the long mapping set of C[Delta^2], the chain {0,2} subset {0,1,2} is oriented from the long arrow to the composite. Consequently H^rev, not H, has the needed endpoints. The sole composition involving two nonidentity arrows lands at {0,1,2}, whose image is gf; all others are units. Thus there really is an enriched functor, and restrictions give precisely the three desired boundary arrows. Repeating with J^rev supplies the second triangle. The definition of equivalence in `def-cbc-enhanced-diagrams-cones` is exactly the two inverse-triangle criterion. Universe inclusion acts on these same enriched maps by postcomposition and hence preserves each restriction; it does not choose a new representative edge.

I tested the empty Kan complex, the one-point complex, discrete disconnected Kan complexes and identity maps. If A is empty and f is a weak equivalence, the component bijection forces B empty too; otherwise no conclusion for an impossible weak-equivalence map is needed. On discrete complexes the map is bijective and all displayed triangles are degenerate or strict inverse triangles. For general disconnected complexes, all-basepoint hypotheses and Kan horn filling are unchanged. Smallness is preserved since the witnesses are maps between W-small simplicial sets, with finite simplex factors; finite products and function sets stay in W. No connectedness, nonemptiness or larger-value-universe hypothesis has been smuggled into an application.

I checked delivery-errors B-E against the files. There are no new unsplit statements, duplicate nodes, relabelled clauses, or hidden non-elementary claims. The two non-elementary inputs are existing cited statements, whose applicable clauses are verbatim in citations.json. The horn argument and enriched-functor checks are written out. The proof dependency list is exactly the union of step uses. The two off-unit lemmas are declared as generic tools in split_report.tool_uses. Every step is below 2000 characters (541, 833, 1427); no long step conceals a comparison lemma. No SGA source is used. All writes remain in the item sandbox; no Lean/compiler/Lake or local DAG-check tools were run.

## Unfinished work

No mathematical gap remains in this one-level split. The two existing non-elementary dependencies retain their own proof obligations; they are cited as statements rather than re-split. Server preflight and delivery results follow from the required delivery commands.
