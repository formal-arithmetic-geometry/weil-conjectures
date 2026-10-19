# Stage-1 delivery: lem-coef-infinity-left-pinch-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-left-pinch-comparison.json`: existing statement, now split into six steps; not a Mathlib leaf. Statement, statement dependencies and source retained. Existing imported search records retained; five searches made by Q34 appended.
- `citations.json`: seven step/node entries, each quoting the relevant cited statement verbatim.
- `searches.jsonl`: actual msearch.py records for this delivery.
- `report.md`: this report.

There are **0 new nodes and 0 Mathlib leaves**. The sandbox initially contained only dispatcher markers; there was no previous split or report to recover.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint id and for `pinch`/`left-pinch`, and searched the exact upstream master reference for the same notions. No project declaration states the item. This is not an attachment claim based on an upstream sorry.

## Literature wanted

WANTED: archived Kerodon Subsection 4.6.5, especially Construction 4.6.5.1 (01KX), Proposition 4.6.5.5 (01L0), Construction 4.6.5.7 (01L2) and Proposition 4.6.5.10 (01L5), for lem-coef-infinity-left-pinch-comparison. Read these pages online; no download or change to literature/ was made. `proof_origin.by` is `agent`, as required for the explicit argument with an unarchived reference. These are Kerodon tags, not unrelated Stacks tags. No Stacks tag states this quasicategorical result; no SGA source was used.

## What was wrong or missing

The existing item was statement-only, with no proof and no Lean audit providing a finished declaration. Its statement is correct and is unchanged. The current blueprint `main-20261015/.../sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2, was read: this item supplies a coherent mapping-space tool in that paragraph's existing dependency ancestry. The inherited unit binding is `sk-prop-sf-biduality-general`; I read its unit and the six-functors chapter, left their metadata fixed, and did not replace any unit proof route. This item is not the key statement of that unit.

The DAG already has `lem-coef-simplicial-opposite-homotopy-calculus`, but using it here creates a dependency cycle through `lem-coef-kan-quillen-right-proper`, Brown localization, Quillen B, sharp pullbacks, and the cocartesian mapping criterion back to this item. I did not cite it. The particular elementary reversal operations needed here are written as explicit formulas in steps 1–4 and 5. In contrast, the existing right-pinch comparison has no return path to this item (95 nodes in its dependency closure checked), so it is a valid dependency.

## Searches and reuse

Before writing, searched the whole DAG for 01L5, left-pinch, pinched mapping spaces and opposite/homotopy calculus. Read the statements of the right-pinch comparison, the opposite calculus, opposite/subdivision Kan zigzag, marked opposite calculus, and the cocartesian mapping criterion. `tools/blueprint_refs.py search` for `pinch`, `mapping space`, and `opposite` found no equivalent blueprint theorem; `ancestor` returned `prop-coef-integral-exceptional-adjoint`. No new statement is needed. The left/right pinch distinction is preserved rather than merging the item with its right-handed input.

Ran msearch.py with this item and group for LeanFinder (two phrasings), Loogle, LeanSearch and grep. All five services/queries completed successfully; their exact queries and results are in searches.jsonl and appended to the item's records. The original records were preserved as prior work, not claimed as Q34 searches. Read Mathlib's `Quasicategory/TwoTruncated.lean:78-87` (relations on edges, not all-dimensional mapping complexes), `SimplicialSet/Op.lean:42-89` (opposite involution, not the pinch comparison), and the ordinary-arrow opposite hit in `CategoryTheory/Comma/CardinalArrow.lean`. Loogle's quasicategory results give horn-filling definitions and consequences, not this theorem. Hence no exact match or one-line specialization was found for the item.

## Review by Q34

I read [Kerodon 01L5](https://kerodon.net/tag/01L5), [01L2](https://kerodon.net/tag/01L2), [01KX](https://kerodon.net/tag/01KX) and [01L0](https://kerodon.net/tag/01L0). They give the two pinched models, their Kan property and the pinch equivalences. This proof uses the already stated right-handed theorem rather than reintroducing the left-handed conclusion as a new lemma. There are no new nodes whose source needs a separate review.

For step 1 I opened `def-cbc-enhanced-diagrams-cones`: its statement defines all horns and includes outer horns for Kan complexes, with no dimension-zero nonemptiness assumption. Reversing vertices takes the omitted face index i to n-i. The displayed involution identities therefore turn each horn problem into precisely the one claimed; inner indices remain inner, and arbitrary indices remain allowed for Kan complexes. This is a direct change of variables in the stated definition, not a use of model-category theory.

For step 2 the same definition node explicitly gives the right-pinched convention: the **entire** initial face is constant, and the new last vertex goes to the new last vertex under operators. Reversing sends the item's entire final face constant at b to this entire initial face and sends its first vertex a to the last vertex. I checked `(alpha^L)^vee=(alpha^vee)^+` separately on the old vertices and on the new last vertex. This proves compatibility with degeneracies as well as faces. No merely vertexwise constancy is substituted for simplexwise constancy.

For step 3 I opened both cited statements. The right-pinch node defines U as the strict fiber of the internal arrow object at **both endpoint simplices**; the definition node makes the internal functor m-simplices maps from `Delta^1 x Delta^m`. Exchanging factors puts that in the product convention used in the proof. Reversing both parameter and interval interchanges a,b and the operator alpha becomes alpha^vee. Thus the codomain is the **opposite** of the arrow fiber in D^op, not an incorrectly unreversed fiber. Products being degreewise is explicitly in the cited definition statement.

For step 4 I read the actual formula for the right-pinch map in its node, not just its title. Evaluating the conjugated order map on the bottom and top layers gives 0 and i+1, respectively. Since the maps in question come from maps of posets, their agreement on objects gives agreement on every chain, hence on all nerve simplices. This supplies the actual square of maps. The separate alpha identity proves the left-pinch formula is simplicial; neither compatibility is dismissed as an unspecified transport.

For step 5 the cited right-pinch statement explicitly says **both** complexes are Kan and the specified map is a homotopy equivalence. Its sole category hypothesis holds by the horn calculation of step 1; b and a are vertices of D^op with no further assumption. Reversing a cylinder homotopy uses the degreewise product rule and the explicit interval-reversal isomorphism from step 1, and interchanges its two endpoint equations. It gives the inverse homotopies for the opposite map directly, without invoking a Whitehead theorem, fibrancy replacement or right-properness. Thus this step has exactly one non-elementary input and cites it. I checked that no existence of an edge between a and b is used.

For step 6 the definition node says enhanced functors are simplicial maps; the two endpoint conditions therefore remain true after postcomposition. The displayed equality is associativity of composition in each degree and proves strict naturality of j^L for every such functor, independent of choices of inverse homotopies. No extra full-faithfulness or equivalence hypothesis was added.

I checked B1–B10: no new unsplit nodes, no new definitions or leaves, preserved source/blueprint metadata, precise endpoint definitions, exact logged searches, and no finished attachment overlooked. For C1–C8 I compared each cited statement with its use, provided verbatim quotes for all seven citations, and checked absence of a return path for the chosen theorem; there is no off-unit proof dependency. For D1–D5 the six steps compute the operator, arrow, pinch and naturality identities; they do not relabel the conclusion into a new node or appeal to a cited node's hidden proof. For E1–E7 the only hypothesis of the right comparison is explicitly established; the two models and parameter opposites are kept distinct; no statement correction or unrecorded source error was required.

Small cases checked: m=0 gives an edge a to b, and both pinch formulas are the identity on that edge; m=1 sends (0,0),(1,0) to 0 and (0,1),(1,1) to 1,2, matching reversal of the right prism. An ordinary category with no arrow a to b gives empty mapping complexes, which remain Kan and are handled without selecting a point. The terminal category gives singleton complexes in every degree. When a=b, degeneracies give the constant edge and no formula requires distinct endpoints. Identity and composite functors obey the same strict postcomposition equation. These checks revealed no missing hypothesis.

The only non-elementary step is 5, at 1123 characters. No step exceeds 2000 characters, and no inline non-elementary comparison has been hidden in a long step: the other steps are direct operator/product/poset calculations from the cited definitions and the maps explicitly specified in the item.

## What remains

No mathematical part of this split is left unfinished. The existing right-pinch theorem remains its own DAG item/approved split; this delivery does not claim to close its Lean proof. Remote dry-run results are recorded below after the check completes.
