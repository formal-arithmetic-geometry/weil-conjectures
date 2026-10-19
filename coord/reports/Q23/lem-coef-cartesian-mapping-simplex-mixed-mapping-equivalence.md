# Stage-1 report: lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence

## Files written

- dag/nodes/sec-six-functors/lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence.json: statement, split into four proof steps; statement unchanged; not a Mathlib leaf.
- citations.json: one verbatim statement excerpt for each of the five step/node citations.
- searches.jsonl: four fresh searches run through msearch.py, retaining the actual results. The item's earlier recorded searches are also retained.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit realization record changes: this item is not a unit's key node.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the exact item tag/id and mixed/coherent mapping, Cartesian edges and Cartesian fibrations. There is no project declaration stating this item. Ordinary Hilbert-scheme Cartesian squares are unrelated. The read-only upstream master source is reference material only; no sorry declaration was counted as a proof.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Propositions 2.4.4.3 (printed p. 131), 2.2.4.1 (printed p. 88), and 3.2.2.10 (printed pp. 183-184), archival copy in literature/, for lem-coef-cartesian-mapping-simplex-mixed-mapping-equivalence. The cited IAS URL timed out. I read the author's online Harvard PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf, including the displayed Cartesian mapping square and the mixed coherent-mapping square. No download or modification of literature/ was made. Because the source is not archived, proof_origin.by is agent.

## Audit and corrections

The imported node had no proof. Its statement is correct and remains unchanged. HTT 3.2.2.10 says its bottom horizontal arrow is a weak homotopy equivalence because the indicated edge is Cartesian; the present split spells out why. I used two existing nodes instead of introducing new versions of their assertions:

- lem-coef-infinity-cartesian-mapping-criterion supplies the homotopy Cartesian mapping square for an inner fibration between quasicategories.
- lem-coef-rigidification-postcomposition-comparison supplies preservation of the specified postcomposition map when passing to coherent realization, without imposing a Kan condition on its raw mapping sets.

The elementary calculation between them is specific to the ordered base simplex: both base right-pinched mapping spaces have exactly one simplex in every degree. Their path-space homotopy pullback is therefore exactly the upper right mapping space. This calculation is a proof step rather than a new node. No statement dispute, extra hypothesis, route replacement or SGA citation is involved.

Read dag/chapters/sec-six-functors.json and dag/units/sk-prop-sf-biduality-general.json. The item's historical blueprint ancestor is prop-coef-integral-exceptional-adjoint, proof paragraph 2, through the inherited chain and step 12 of lem-coef-cartesian-base-equivalence-invariance. I read that paragraph in the master snapshot and the current main-20261015 ancestor under sk-thm-sf-package, whose file contains the same statement and no proof text. I retained the maintainer-owned historical unit and blueprint ancestry. All proof citations belong to the item's existing unit, so no off-unit tool declaration is needed. The new proof realizes the precise foundation already requested by its parent; it does not replace any unit-level argument.

## Search evidence and duplicate checks

Read all inherited Mathlib search results and retained their records. Fresh msearch.py queries, with the actual query strings preserved in mathlib_searches and searches.jsonl, were: a semantic search for coherent postcomposition over an ordered simplex (LeanFinder), a differently phrased search using the nerve of a partially ordered set (LeanSearch), Loogle with the quoted substrings SSet and Cartesian, and a grep for coherent realization/Cartesian edges/Cartesian mapping in AlgebraicTopology. Loogle and grep had no hits. LeanFinder returned horn filling, strict Segal structures, edge composition witnesses and the ordinary Kan-Quillen fibrations. LeanSearch returned ordinary-category Cartesian lifts, ordinary nerve edges and the 2-truncated nerve adjunction. None asserts the present enriched/quasicategorical comparison.

I read Mathlib/AlgebraicTopology/SimplicialNerve.lean lines 12-35, whose project list still asks for the locally Kan coherent-nerve quasicategory theorem; Nerve.lean lines 166-173 state only the edge/Hom bijection, and NerveAdjunction.lean lines 282-300 only the 2-truncated adjunction. These do not finish this item. No Mathlib assertion was guessed or recorded as a match.

Searched the whole DAG for mapping criteria, postcomposition, rigidification, and HTT 2.4.4.3, and ran blueprint_refs.py ancestor plus searches for Cartesian, Cartesian edge, 2.4.4.3, coherent realization and postcomposition. The existing two comparison nodes are used directly; no new duplicate or rephrased clause was created. Blueprint same_as remains empty: the ancestor is an adjunction theorem, not another statement of the present simplicial assertion. Direct dependency traversal confirmed that the relative calculus, Cartesian mapping criterion, and rigidification comparison do not depend on this item.

## Unfinished work

No unresolved issue in this split. The external source archive is requested above. This is a stage-1 DAG delivery, with no Lean writing, compiler run, Lake run or claim of having completed the dependent Lean proofs.

## Review by Q23

I checked delivery-errors B through E against the actual node statements and the online source. There are no new nodes needing statement-only forms, search records or tag distinctions. Every proof step has a source and its exact dependencies; proof_deps is the union of uses. The statement introduces all its objects and retains the inherited notion dependencies. No definition was substituted for a theorem and no part of a cited proof was silently used.

For step 1 I read the definitions of standard simplices and inner horns in def-cbc-enhanced-diagrams-cones, and the last paragraph of lem-coef-relative-marked-anodyne-calculus. The first gives the monotone-vertex calculation written out in the step; the second explicitly guarantees quasicategorical total space over a quasicategory. Cartesian fibration includes inner fibration in the same node's opening paragraph. Thus the mapping criterion's hypotheses hold before it is applied. Every consecutive edge lies in an inner horn, including the m=2 horn containing 01 and 12, so the simplex-filling argument has no low-dimensional exception.

For step 2 I read the full right-pinched mapping-space definition in def-cbc-enhanced-diagrams-cones and copied it into citations.json. The entire initial face is constant, not just its vertices in an arbitrary target. In the target simplex, a simplex is determined by its ordered vertices, so the only possible m-simplex is the sequence (i,...,i,j). It exists exactly when i<=j. The hypothesis p(z)<=p(a) and monotonicity of p(e) give this inequality for both pairs. This is a degreewise computation, marked elementary, and hides no comparison lemma.

For step 3 I read the statement of lem-coef-infinity-cartesian-mapping-criterion, including its path-space definition of homotopy pullback, and compared its orientation to HTT 2.4.4.3. It is Cartesian/postcomposition, with maps out of z; the cocartesian/precomposition version would be the wrong one. The actual edge e is Cartesian by the item's hypothesis. After step 2 the path coordinate and both base coordinates are unique, so the path fiber product is canonically Map_Y(z,b). Its comparison from Map_Y(z,a) is precisely postcomposition. This verifies the map, rather than merely the existence of some weak equivalence between the spaces. No right-properness theorem or unproved strict/homotopy pullback replacement is needed for this point-base calculation.

For step 4 I read all of lem-coef-rigidification-postcomposition-comparison. Its consequent explicitly states that the actual simplicial composition by the vertex [h] is a weak homotopy equivalence whenever mapping-space postcomposition is one. With S=Y, h=e and source vertex z, step 3 supplies exactly that premise. The statement explicitly disclaims a local Kan hypothesis on the raw coherent realization. This is the additional content needed beyond a bare weak equivalence of two mapping-space models. The locally Kan comparison in lem-coef-coherent-nerve-comparison alone would not justify the conclusion for raw mathfrak C[Y]; I used the dedicated existing comparison that does say it. Its source agrees with HTT 2.2.4.1 and the mixed-square use in 3.2.2.10.

Edge cases checked: n=1, equality of any of u,v,w, a vertical Cartesian edge, a degenerate identity edge, and empty source/target mapping spaces. For empty spaces the point-base pullback is still B, and the criterion forces emptiness on both sides together. No nonemptiness was introduced. The earlier-vertex condition is essential: for p=id on Delta^1, e=0->1 and z=1, the source mapping space is empty and the target a point, so removing that condition would be false. This counterexample does not satisfy the stated condition and requires no correction to the item.

I checked the long-step rule: lengths are 793, 581, 941 and 634 characters, all below 2000. The non-elementary inputs are precisely the cited total-space fact, Cartesian mapping criterion and rigidification postcomposition theorem. Each quotation is copied verbatim from the cited statement. There is no new lemma hiding in a long proof step, no circular citation and no new node restating a clause of the item. The source reading and hypothesis checks required no statement correction.
