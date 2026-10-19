# Stage-1 report: lem-coef-segal-cotensor-evaluation-dk

## Files written

- dag/nodes/sec-six-functors/lem-coef-segal-cotensor-evaluation-dk.json — statement, split; unchanged statement, eight proof steps, no Mathlib match.
- citations.json — fifteen step/node entries with verbatim quotations of the statements used.
- report.md — this report. No new nodes, no Mathlib leaves, and no unit changes.

## Attachments

None. Searched the project declarations under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item's blueprint tag, Segal, Dwyer, walking isomorphism, and cotensor/evaluation. There is no exact project declaration. The exact upstream master was also checked as reference material, not as evidence of a finished proof. Mathlib searches ran through msearch.py and are recorded in searches.jsonl and the item. The returned strict-Segal, nerve, ordinary fully-faithful-functor, and locally constant condensed-functor declarations do not concern the Reedy-fibrant Segal-space exponential in this statement. I read their source signatures, including NerveAdjunction.lean:370–407, StrictSegal.lean:35–65, Coskeletal.lean:45–85, Functor/FullyFaithful.lean:35–70 and Condensed/Discrete/LocallyConstant.lean:378–395. Two semantic phrasings were tried. There is no Mathlib leaf to attach.

## WANTED

WANTED: Charles Rezk, *A model for the homotopy theory of homotopy theory*, Sections 2.3–2.5, 6, 7.3–7.5, 12.2–12.4 and 13.5–13.9, especially printed pp.31–32, for lem-coef-segal-cotensor-evaluation-dk. Read the Rochester-hosted PDF online; it is not archived in literature/. The proof_origin is agent and points to the current blueprint ancestor, recording that this is an expansion of the online Rezk argument. No Stacks tag states this Segal-space theorem; no SGA source is used.

## What was wrong or incomplete

The item arrived with a statement and no proof. Rezk's Lemma 13.9 leaves the identity-square calculation to a computation using Lemma 12.4. This delivery writes the computation, identifies the actual maps and their fixed-endpoint fibers, and proves the homotopy-monomorphism cancellation including component surjectivity. It does not use the parent categorical-equivalence/DK criterion: that parent cites this item and would create a cycle. The item statement is correct and unchanged. The assignment initially preceded the local snapshot update; the original node appeared during the normal shared refresh and was then copied, with its original metadata retained.

## What could not be finished

No mathematical part remains in this one-level split. The external source still needs archiving. Server validation is recorded below after the dry run; no delivery is pushed by this worker.

## Not duplicates

No new node was created. Whole-DAG keyword searches, blueprint_refs.py searches for Segal, cotensor evaluation, homotopy monomorphism and Segal identity, and the Lean-source searches found no replacement for the entire item. The existing lem-coef-segal-equivalence-classifier is exactly the needed Theorem 6.2; it is cited rather than duplicated. The existing contractible-fiber criterion, cartesian-exponent theorem and DK two-out-of-six theorem are also reused. The inverse-evaluation node is an alternative formulation of the classifier, not an additional dependency needed here.

## Review by Q25

I read Rezk's Lemma 13.9 and the preceding first paragraph of Proposition 13.8, together with the displayed squares and Lemma 12.4 in the Rochester PDF. I also read the current main-20261015 ancestor proof paragraph 2, the six-functor chapter and the bound unit. This is inherited mapping-space infrastructure below that unit; the chapter and unit routes do not change. I opened every cited node and checked its statement, rather than importing facts from its proof. All cited statements are in the item's unit, and there are no off-unit tool uses.

Step 1 uses the cartesian-exponent statement for Segal exponentials and restriction fibrations, Reedy's statement for objectwise fibrancy, and Kan–Quillen for the strict-fiber/homotopy-fiber interpretation. The maps used are inclusions of actual outer simplicial subspaces, so the degree-zero restriction clause applies. All spaces and shapes are small. It does not assume that arbitrary cotensors are levelwise equivalent to W.

Step 2 is an explicit construction: the indiscrete groupoid accepts every object function, so h_i exists, and evaluation and currying give the stated categorical homotopy. The cartesian-exponent node ensures that the target A is Segal. The homotopy-category product is checked on the strict mapping fibers and on their degree-two compositions. The image of the unique invertible arrow gives the natural isomorphism and its inverse, not just an objectwise association. This only proves an ordinary equivalence at this point, so it does not use the parent Proposition 13.8.

Step 3 uses the classifier's exact statement that (V^E)_0 maps by a weak equivalence onto the union of invertible components of V_1. Currying identifies these maps with r_n, and the exponent node permits V=W^{F(n)}. The contractible-fiber criterion says precisely that the fibers of this weak equivalence are contractible. The excluded components have empty fibers; a union of components cannot create a path to an excluded component. Products give the corresponding statement for r_0 squared.

Step 4 is the actual two-triangle decomposition of the square, with the common edge d_1 on both triangles. During self-review I corrected the order in which the triangles were listed: the first is ((0,0),(1,0),(1,1)), so d_2 of that triangle is the source endpoint arrow; the second is ((0,0),(0,1),(1,1)), so d_0 of that triangle is the target endpoint arrow. This makes both the endpoint map and the degeneracy pair (s_0,s_1) agree exactly. No new theorem is hidden in the decomposition: it is verified on increasing strings of square vertices.

Step 5 uses the exponent theorem for Kan fibrations on each of the three two-edge shapes and the Kan model statement for trivial fibrations, their pullbacks, and weak-equivalence cancellation. The consecutive-edge restriction is a weak equivalence by the Segal hypothesis already in the item. The identities d_0 s_0=1, d_1 s_0=1, d_1 s_1=1 and d_2 s_1=1 show explicitly which maps have sections. The nonconsecutive-edge restrictions are only asserted to be fibrations until the degeneracy-section argument proves them trivial; no outer-horn weak equivalence is assumed. The common-diagonal map of the two identity-edge triangles is a trivial fibration over W_0 squared, so the same is true after fixing x,y. Its section is exactly the map induced by s, establishing the composite TJ as a weak equivalence.

Step 6 uses only the already proved fiber description of r_1 and r_0 squared, the contractible-fiber criterion, Kan–Quillen's homotopy-pullback model, and the existing homotopy-pullback invariance statement. The iterated-fiber comparison retains the endpoint paths: its data are an edge lift, its comparison path, and an identification of the endpoint lift with (b,1). The base fiber is nonempty because b is specified, hence contractible. The invariance theorem applies to the cospans over that contractible Kan space with identity map on the possibly empty source. This proves the empty-or-contractible assertion for fibers of T without presuming that r is fully faithful.

Step 7 adds the missing surjectivity argument: TJ is onto components, so T is onto components. This removes the empty alternative for each homotopy fiber of T. The contractible-fiber node now gives that T is a weak equivalence; cancellation gives J. Step 8 uses exactly the two-out-of-six node's formulation on 1_W,j,p_i; its consecutive composites are j and 1_W, so it supplies both evaluations. There is no use of a two-out-of-three clause absent from that node's statement.

I tested the unchanged statement on W empty (all categories and fibers are empty), the discrete nerve of [1] (all invertible diagrams are constant), and the discrete nerve of a one-object groupoid BG with nontrivial G. In the latter case (W^E)_0 has one object for every g in G while W_0 has one object, so evaluation is not a degree-zero weak equivalence. The proof correctly asserts only DK equivalence. Empty mapping fibers and disconnected bases are permitted throughout; the cancellation argument explicitly covers the empty case. No completeness, object-surjectivity, connectedness, or nonemptiness hypothesis was added. The uses/proof_deps union and the verbatim quotations were checked, and a read-only dependency traversal found no path from any cited node back to the item. B–E checks found no new statement to audit, no duplicate, no clause moved into a new node, no source error, and no unrecorded search.
## Second reading by Q25

- Item statement checked clause by clause against Rezk Lemma 13.9 (PDF pp. 31--32), including the definitions of $E$, $p_i$, $j$, and the no-completeness hypothesis; verdict: agrees.
- Step 1 checked against Rezk Lemma 13.9 pp. 31--32 and the cartesian-exponent, Reedy, and Kan node statements; endpoint restrictions are Kan fibrations and all degree-zero spaces are Kan; verdict: sound.
- Step 2 checked against the first paragraph of Proposition 13.8 and the explicit groupoid contraction; the product mapping-fiber and natural-isomorphism argument is substantive; verdict: sound, reclassified non-elementary.
- Step 3 checked against Rezk Lemma 13.9 and the equivalence-classifier and contractible-fiber statements; the componentwise empty-or-contractible fiber conclusion and product case match; verdict: sound.
- Step 4 checked against the square decomposition in Rezk Lemma 13.9; the two triangles, common diagonal, endpoint faces, and degeneracies are identified with the stated simplicial identities; verdict: sound and elementary.
- Step 5 checked against Rezk Lemma 13.9 and the Segal restriction-fibration argument; identity-edge pullbacks, sections, two-out-of-three, and the fixed-endpoint mapping-fiber map are all justified; verdict: sound.
- Step 6 checked against the homotopy-fiber cancellation argument in Rezk Section 12.2 and the homotopy-pullback invariance node; endpoint paths are retained and the empty case is covered; verdict: sound.
- Step 7 checked against the contractible-fiber criterion and the component-surjectivity conclusion; the empty mapping-space case is explicitly handled; verdict: sound.
- Step 8 checked against the existing Segal Dwyer--Kan two-out-of-six statement; the three maps and both successive composites have the required types and equivalences; verdict: sound.
- No new nodes were created, so B1--B7, duplicate-node, source-tag, and Mathlib-leaf checks are vacuous; the existing seven cited nodes were opened and their quoted statements match the uses.
- Changed step 2's `elementary` flag to `false` because its categorical contraction and naturality argument is longer than a two-line definitional check.
- Added the Reedy model-structure citation to steps 5 and 7 and recorded verbatim quotations in `citations.json`, since both invoke two-out-of-three for weak equivalences.

