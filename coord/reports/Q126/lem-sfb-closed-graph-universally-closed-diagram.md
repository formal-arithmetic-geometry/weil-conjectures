# Worker report

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-closed-graph-universally-closed-diagram.json, statement, now Mathlib leaf; citations.json (empty because a leaf has no proof steps). No new nodes. Search receipts remain in searches.jsonl.
2. Attachments: none. Searched WeilConjectures for the exact blueprint tag, closed graph and UniversallyClosed; no project declaration gives every clause. Mathlib declarations are recorded as a leaf, not an attachment.
3. WANTED: none.
4. The statement is correct and unchanged. The imported search conclusion missed CategoryTheory.Limits.pullback_lift_diagonal_isPullback: its name does not contain graph. The second semantic wording found that exact theorem, making the complete package a Mathlib leaf under the one-declaration-per-clause convention. The source is Stacks 04NX (spaces-morphisms-lemma-universally-closed-permanence) proof (1); I also read its scheme counterpart 01W6 (morphisms-lemma-image-proper-scheme-closed), 01W3 and 01W4, and schemes-lemma-semi-diagonal. No SGA source used.
5. Unfinished work: none; delivery verification follows below.

## Review by Q126

I read delivery-errors B through E in both copies. There is no new statement-only lemma, no duplicate or relocated clause, and no source or statement dispute. The item's four statement dependencies were retained: def-pc-scheme supplies schemes, def-pc-fibre-product supplies projections and the universal property, def-weil-proper-morphism explicitly defines separated and universally closed, and def-weil-closed-immersion supplies closed immersions. The definition nodes and the existing lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-integral-separated-uc and lem-weil-pbc-universally-closed-product-map were opened and their actual statements read while considering a split. They need not be cited by a Mathlib leaf. The unrelated stronger ideal-sheaf and base-changed diagonal nodes were not used. Whole-blueprint searches for universally closed, closed graph, closed immersion, 04NX and relative self-product gave no equivalent full package. The existing blueprint provenance is preserved; ancestor reports None, not an identifiable blueprint id, and this is reported rather than invented.

There are no proof steps or step citations in a Mathlib leaf, so citations.json is empty. Instead I checked every clause directly against its Mathlib statement, with exact lines in mathlib_match.how:

- Cartesian graph square: Diagonal.lean:396-399, specialized g=f and the theorem's f=q. Its top and left arrows are exactly f and the graph; the bottom pullback.map has components f after the first projection and the second projection. Rewrite f ≫ q to p using the given triangle. No hypothesis other than schemes having pullbacks is needed.
- Closed graph: Separated.lean:138-139 has the same pullback.lift with identity first component, under exactly IsSeparated q; universal closedness of p is not used here. The leanfinder hit supplies its full generated name IsSeparated.instIsClosedImmersionLiftSchemeId, which I checked against the source's anonymous instance.
- Factorization: HasPullback.lean:180-181 is lift_snd for this graph. Universal closedness of f is exactly Proper.lean:111-113 under UniversallyClosed (f ≫ q) and IsSeparated q; the first is the hypothesis after rewriting the triangle.
- Relative self-product: pr_1 is pullback.fst f f, a base change of the second copy of f, so UniversallyClosed.lean:95-97 supplies its instance. universallyClosedTypeComp at 87-89 applied to this projection and p gives precisely p_2. This uses no properness, compactness or finiteness assumption.
- Arbitrary T: MorphismProperty/Limits.lean:231-235 applies with S=B, S'=T, v_12=p, v_22=q, g=f and base arrow h. Its only equation is p=f ≫ q; its conclusion is the lift with projections f after pr_A and pr_T, exactly f_T. UniversallyClosed.lean:65-66 supplies stability under base change. Thus the T in the statement is arbitrary, including nonreduced schemes.
- Closed maps: UniversallyClosed.lean:49-50 applied to p and p_2 states IsClosedMap, exactly the last sentence. It is closedness of images of arbitrary closed subsets, not merely closedness of the total image.

These are individual direct Mathlib applications, including ordinary typeclass instances, not a multi-lemma comparison with a different geometric definition. The definition matches already in the DAG identify the same notions. All newly recorded searches were run through msearch.py and actual outputs were read; historical searches were retained. The unsuccessful Loogle graph-name queries are recorded as unsuccessful queries, not evidence of absence after the exact semantic hit was found. No proof argument is hidden in a long proof step: the proof list is empty.

I tested the empty A case, the identity f case and a nonreduced test T. Empty graphs and self-products have closed maps; when f is identity, the graph is the diagonal and p_2=p; arbitrary nonreduced T is permitted by the categorical theorem. I also checked that no separation of B, no separatedness of p or f and no finite-type hypothesis has entered. As a necessity check on the given separatedness hypothesis, taking an open chart A=A1 in the doubled-origin line C over B=A1 gives p=id universally closed and q nonseparated, but f is not closed (its chart image is not closed). The statement correctly assumes separation of q.

## Not duplicates

No new nodes were created. Existing nodes supply the same notions and several subclauses; the assigned item remains the combined package and is now a Mathlib leaf.

## Delivery verification

The first server dry run required proof_origin even for a Mathlib leaf. Added the already-read Stacks 04NX source provenance, retaining the empty proof and dependency lists and the Mathlib match. No mathematical change was needed.
