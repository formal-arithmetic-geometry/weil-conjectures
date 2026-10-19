# Stage-1 report: lem-coef-kan-fiber-path-reversal

## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-fiber-path-reversal.json`: statement, split into five proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-walking-isomorphism-edge-anodyne.json`: new statement-only unsplit lemma; no Mathlib match after both semantic phrasings, Loogle, LeanSearch and source grep.
- `citations.json`: verbatim statement excerpts for every step/dependency pair.
- `searches.jsonl`: actual msearch records, retained unchanged.

There was no earlier sandbox node, report or search log to resume. The item was copied from the shared repository; all writes are confined to this sandbox. No Lean, compiler, Lake, local DAG validation script, or git command was run.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for path reversal, Kan-fiber and walking-isomorphism terminology; also checked `dag/lean_names_upstream.json`. The path-reversal item has no project declaration. The upstream master reference search did not provide a finished proof. Mathlib's abstract `PathObject.symm` only interchanges structural projections, and the truncated edge-homotopy symmetry declarations do not construct the required maps and endpoint-fixed homotopies.

## Wanted sources

WANTED: archival Kerodon Subsection 3.1.2, Definition 3.1.2.1 and Remark 3.1.2.6 (https://kerodon.net/tag/00UG), for lem-coef-walking-isomorphism-edge-anodyne.

WANTED: archival Kerodon Corollaries 3.1.3.3 and 3.1.3.6 (https://kerodon.net/tag/00TM and https://kerodon.net/tag/00UT), and Example 3.1.8.10 (https://kerodon.net/tag/0101), for lem-coef-kan-fiber-path-reversal.

These were read online, not downloaded or represented as archived literature. The item's proof is explicitly agent-written. The new edge lemma is an agent-formulated consequence, not claimed to be the text of a Kerodon theorem. There is no Stacks tag for that particular assertion. The existing arbitrary-monomorphism lifting leaf has the exact Stacks source Tag 08NM, `simplicial.tex`, label `lemma-trivial-kan`; I read that source and its proof.

## Problems found and changes

The imported statement is valid and is unchanged, including strict projection compatibility, actual product-with-Delta-one homotopies, arbitrary simplicial r and possible empty X. No STATEMENT-DISPUTED correction is needed. The empty proof is now an argument rather than a reference. Its crucial distinction is that reversing the order of the vertices of Delta-one does not define a simplicial endomorphism. Reversal instead uses a chosen extension to the nerve of the two-object groupoid.

The chapter and unit were read. The item is not the unit's key node, so no unit realization fields are changed. Its recorded ancestor is prop-coef-integral-exceptional-adjoint, paragraph 2, the displayed derived coefficient-adjunction calculation. I read its current main-20261015 proof. The split supplies the finite-core fiber-contraction infrastructure along the existing ancestry, without replacing a unit step or changing coefficient categories. The item and child both retain that ancestry and specify the particular supporting place.

## What remains

The new walking-isomorphism edge-anodyneness lemma is intentionally left unsplit, with no proof or proof dependencies in its node. There is one new node and zero new Mathlib leaves. No other part of the item's proof remains unaccounted for.

For the next worker, here is the intended argument for that child (report only). An n-simplex of J is a binary word of length n+1, with faces deleting a letter and degeneracies repeating one. Its nondegenerate simplices are exactly alternating words. Start with K_1 equal to the forward edge 01 and its vertices. For n at least 2, adjoin the alternating n-simplex a_n starting at 0, by its horn Lambda_0^n. Its last face is a_(n-1), already present (a_1=01); each internal face has adjacent equal letters and is a degeneracy of a lower-dimensional alternating word already present. The missing face d_0 a_n is the alternating (n-1)-simplex starting at 1, not previously present. Consequently this pushout adds exactly a_n and d_0 a_n and their degeneracies; all their remaining proper faces are in K_(n-1). This can be checked directly by the word formulas, so the pushout identifies no old simplices. The union of the K_n is J: every alternating word starting at 0 is some a_n, and every positive-dimensional one starting at 1 is d_0 a_(n+1). All words with adjacent repetitions are degeneracies of these. Given any lifting square against a Kan fibration, extend successively using its Lambda_0^n lifts and take the degreewise union at omega. The extensions agree on the preceding K_n, so the two filler equalities hold on J. This proves the child's precise left-lifting assertion without realization theory, an implicit groupoid-completion comparison, or inner-anodyne cancellation. Checks n=2 and n=3 add respectively (10,010) and (101,0101). The child is genuinely a shape lemma independent of X,Y,r,y, and does not restate any clause about the item's path fibers.

## Not duplicates

lem-coef-walking-isomorphism-edge-anodyne vs lem-coef-joyal-walking-isomorphism-fibration-test: the latter tests Joyal fibrations by a vertex-to-J inclusion and inner horns; it does not assert that the edge Delta-one-to-J is Kan anodyne.

lem-coef-walking-isomorphism-edge-anodyne vs lem-coef-quasicategory-invertible-interval: the latter gives endpoint evaluation and existence of J-diagrams from isomorphisms, not the edge inclusion's left lifting property against arbitrary Kan fibrations.

lem-coef-walking-isomorphism-edge-anodyne vs lem-coef-edge-inverting-anodyne-extension: the latter assumes an input map is Kan anodyne and proves a diagram-restriction theorem; it does not establish anodyneness of this input map.

lem-coef-walking-isomorphism-edge-anodyne vs lem-coef-simplicial-walking-groupoid-components: the latter concerns framed derived mapping spaces of simplicial categories, not this ordinary nerve inclusion of simplicial sets.

lem-coef-walking-isomorphism-edge-anodyne vs lem-coef-joyal-interval-boundary-tests: the latter uses a different finite simplicial interval with two separately attached inverse witnesses and gives endpoint inclusions, not the forward-edge inclusion into the full groupoid nerve.

The whole DAG was searched by groupoid, walking-isomorphism, edge and anodyne terminology. Blueprint-wide searches by Kan, walking, anodyne and path found no matching imported node. Mathlib CoherentIso.lean was read through its end: it defines the exact shape, its two arrows and inverse triangles, but no anodyne inclusion theorem. The anodyne-directory grep returned no occurrence of coherentIso or WalkingIso. The two semantic phrasings only found horn generators, nerve/Segal structure and cofibration facts. This is not a one-line specialization of those hits.

## Review by Q30

I read the requested delivery-errors sections B through E and checked each issue against the written files. The new child introduces all its objects and universes, defines Kan anodyneness by the actual lifting property, and cites the existing simplicial definitions. Its node carries only a statement. Its JSON uses ordinary TeX escapes once, complete blueprint provenance, and actual search records. No Mathlib leaf is claimed for the child. The original item and its inherited fields, citations and search history are preserved apart from the permitted split fields and the appended actual searches.

For Step 1 I read the whole statement of lem-coef-kan-pullback-path-comparison. It explicitly gives Kan fibrancy for both maps U and V into W without a fibration condition, which is exactly the clause used. Delta-zero is Kan by the unique extension; r is only a map of Kan complexes. The two substitutions exchange U and V rather than invoke an unavailable simplicial interval reversal.

For Step 2 I checked the new child's exact LLP statement and the statement of lem-coef-sset-anodyne-pushout-product. The latter uses the same LLP-against-Kan-fibrations definition; it allows every monomorphism, so the boundary inclusions including dimension zero satisfy its hypothesis. I read the Mathlib declaration SSet.anodyneExtensions_pushoutObjObjι at PushoutProduct.lean:95-103 and the definition at AnodyneExtensions/Basic.lean:70-75. The parameter/source factor order matches the displayed union. The transpose is just the defining Fun formula, not an uncited theorem about exponentials. Kan Y makes Y-to-point the required fibration. I also read def-weil-pbc-trivial-kan-fibration; the m=0 case proves the required surjectivity instead of leaving it implicit.

For Step 3 I read the complete statement of lem-weil-pbc-trivial-kan-lifts-monomorphisms, its Stacks source 08NM, and SSet.rlp_monomorphisms at CategoryWithFibrations.lean:127-132. It permits the empty-to-A inclusion and places no Kan or nonemptiness condition on A. Thus q has a genuine section with q sigma equal to the identity. This section is a choice of proven mathematical data, not a hollow definition. The swap of the two-object groupoid is a functor and squares strictly to the identity because every hom-set is a singleton; taking nerves/precomposition gives theta. I verified the two endpoint equations using q sigma, not an assumed natural reversal of Delta-one.

For Step 4 the same arbitrary-monomorphism statement applies to A times boundary-I into A times I, a degreewise inclusion even for empty A. The two endpoint maps have the identical bottom map T. I checked q theta sigma equals T, t theta sigma equals q sigma equals identity, and all compositions in these equations. Applying evaluation to qH=T pr proves that tH fixes both original endpoints for every parameter simplex. This is the compatibility that the item needs; a bare weak equivalence of total path spaces would not suffice.

For Step 5 I checked both pullback equations with their actual orientations, the simplicial-operator compatibility, the two composite formulas, and the fact that each homotopy leaves x literally unchanged. These are direct substitutions in def-cbc-enhanced-diagrams-cones, whose full statement I read; the step is correctly elementary. Step 2's transpose, Step 3's endpoint check and Step 4's restriction equations are explicitly written and invoke the non-elementary lifting results rather than hiding them behind 'transport'. Each step's uses has a verbatim statement excerpt in citations.json, and proof_deps is exactly their union. No step cites a definition as evidence for an independent theorem.

Small-case checks: for X empty both path fibers and every requested domain are empty. For Y discrete both orientations reduce to the same union of components of X, and T must act identically on their constant paths. For Y the nerve of a groupoid, the construction reduces on vertices to an inverse arrow, and the relative lift witnesses the double inverse. For non-fibrational r, only Kan fibrancy of X and Y is used in Step 1; no later step invokes r as a fibration. A vertex y prevents empty Y but places no condition on X. The new child is valid in its two lowest attachment dimensions as checked above and has no connectivity hypothesis to test. All parameter domains and exponentials stay within the specified common universe.

Every non-elementary ingredient is now a cited node; no new node is elementary, a duplicate, an item clause, or a whole-proof relabelling. All proof steps are shorter than 2000 characters. The one independent combinatorial sublemma was extracted into the new statement-only node instead of hidden in a long step. The path-pullback result and new child belong to this unit; the other non-definition citations are existing Mathlib leaves. No off-unit tool-use declaration is necessary, and no SGA source is used.

## Validation

The first dry run rejected the too-short Kan-fibrancy citation excerpt. I replaced it with the complete setup, displayed path pullback and unconditional Kan assertion copied verbatim from the existing node; the mathematics and proof were unchanged.
