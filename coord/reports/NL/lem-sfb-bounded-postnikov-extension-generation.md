# Worker report: lem-sfb-bounded-postnikov-extension-generation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-postnikov-extension-generation.json`: the item, statement unchanged, seven-step split; no exact Mathlib match.
- `citations.json`: thirteen verbatim quotations, one for each cited node in each proof step.
- `report.md`: this report. `searches.jsonl` is the search command's log; `prepare.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit record needs modification: this item is not its unit's key node.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag, Postnikov/postnikov and extension-closure terminology. The tag is absent. The seven files with broader terminology concern particular sheaf/module extension-closure or algebraic-geometry results, not an arbitrary t-structure or this ordered tower. None supplies an attachment.

## WANTED

None. Read BBD, *Faisceaux pervers*, 1.3.1–1.3.6, printed pp. 29–31 (PDF pp. 30–32), especially the adjunction and uniqueness in 1.3.3, the endpoint and nested-truncation discussion in 1.3.4, and the truncation octahedron in 1.3.5. Read the actual Stacks `derived.tex` remark `remark-truncation-distinguished-triangle`, Tag 08J5, including the successive upper-truncation triangle. These sources are present locally. No SGA source was used.

## Faults and corrections

No statement dispute or route error was found. The current item already explicitly separates arbitrary t-structures from the standard derived-category specialization, gives actual t-bounds on K, fixes the order and length, and includes n=0. I retained this statement and the existing citation/search material. The sandbox had no earlier item, report or search log to repair. The source item had no proof; the delivery now writes the construction rather than replacing it by a node for a tower or for one of its clauses.

The proof does not take arbitrary-t-structure facts from Stacks 08J5, which concerns derived categories. Its abstract input is the existing `lem-weil-heart-short-exact-triangles` statement, whose clause (1) expressly applies without boundedness. The older definition node's narrower sentence about bounded truncations is not used to assert the existence of arbitrary truncations.

One off-unit generic tool is declared in `split_report.tool_uses`: `lem-weil-heart-short-exact-triangles` for truncation adjunctions, triangles and extension closure. This is below the integral-models unit's bounded tensor argument and does not replace any unit-level route.

## Unfinished work

None in this one-level split. No new unsplit dependency was necessary. Dry run and push results are recorded by the delivery command.

## Not duplicates

No new nodes. Blueprint searches for `Postnikov`, `successive truncations`, `t-structure` and `finite ordered`, and a whole-DAG scan of truncation statements, found no other node stating the finite ordered tower for an arbitrary t-structure. `lem-weil-heart-short-exact-triangles` supplies single truncation triangles and their universal properties; `def-kun-truncations` and `lem-weil-pbc-truncation-triangle` concern complexes and the standard derived t-structure. These existing inputs are reused, not recreated. The item's `blueprint.same_as` stays empty, and its already precise `from.place` is retained.

## Review by NL

I checked the statement against BBD 1.3.3–1.3.6 and the explicit triangles of Stacks 08J5. The abstract theorem does not require global boundedness or nondegeneracy; its given finite t-interval is exactly what makes the first truncation zero and the last truncation K. There are no new nodes to source or search.

For step 1 I opened the complete statement of `lem-weil-heart-short-exact-triangles`. Clause (1) states functorial truncations and the right adjunction to the upper aisle for every integer and every t-structure. Its counit therefore gives the displayed Hom bijection, with the inclusion full as required. This is the input actually used; no part of the cited node's proof is treated as its statement.

For step 2 I checked that the test object P is at most q-1 and hence at most q by the shifted t-structure axioms. Both successive Hom bijections are instances of the stated right adjunction. The two maps between A and A' are constructed by these bijections; their composites are identities by uniqueness. This is an elementary two-adjunction argument, not a hidden truncation-commutation theorem and not an uncited application of Yoneda. Compatibility with the counits is explicitly stated, giving the common arrows in the tower.

For step 3 I checked the same node's clauses (1) and (2), and the definition of a triangulated category. The triangle is applied to B at q-1, so its third vertex is exactly the double truncation in the item's own definition of H_t^q(K). Rotation has outer terms B and A'[1]. Their bounds are at most q and at most q-2, respectively, so the extension-closure clause really implies C_q is at most q; its lower bound q comes directly from clause (1). Thus C_q[q] is in the heart. Shift cancellation and invariance under triangle isomorphism are part of the triangulated structure, not comparisons with standard cohomology or identifications of two independently chosen cone objects. I opened all three cited statements and copied the applicable formulas into citations.json.

For step 4 I checked orthogonality at the precise pair of bounds a-1 and a, rather than assuming that zero t-cohomology detects zero in a degenerate t-structure. The right-adjunction bijection makes the endomorphism group of L_0 zero. Its identity is therefore zero, and the zero maps exhibit its isomorphism with the zero object. For step 5 I checked that K itself lies in the full upper aisle at b=a+n-1. The counit has an inverse explicitly produced from the bijection, and the second inverse relation follows by its injectivity. These are elementary consequences of the cited universal properties, not separate endpoint lemmas.

Step 6 uses only the preceding steps: the substitution q=a+j gives precisely the stated factors, on the vertices already constructed, and there are n adjacent pairs. I checked n=0 separately through the same two endpoint arguments, which then identify K with zero without requiring any triangle. No extra node is cited here, so there is no missing quotation for this step.

For step 7 I opened `def-kun-truncations`, `def-sbc-standard-tstructure-derived-category` and `def-weil-abstract-derived-category`. The first statement explicitly supplies both good-truncation formulas and their interpretation as the standard t-truncation functors. Applying the lower truncation to the upper one has one nonzero term, the cokernel into ker d^q, equal to H^q(E); shift by q puts it in degree zero. The other two nodes identify the standard t-structure and descended cohomology. This proves the specialization by direct computation from the cited definitions; no geometric or sheaf-specific concentration theorem is misapplied to arbitrary abelian categories.

I checked the delivery-errors B–E points against the files: no new-node shape, duplicate or unrun-search claim is introduced; every proof citation has a literal statement quotation; the statement is not moved into a new node; every input beyond definitions is the stated generic truncation-and-extension theorem; the proof uses no small-index colimit, completeness, representative boundedness, or nondegeneracy hypothesis. Searches inherited in the repository were retained, and all newly recorded Mathlib searches were run with the mandated command and read. The current searches again return individual truncations, bounds or isZero, not the ordered finite tower. The Loogle tower query returned an unrelated stalk scalar-tower declaration, not a Postnikov theorem.

Small cases checked: n=0, n=1 with K in one heart degree, K=0 with any n, a negative, padding the interval with zero cohomology at either end, and a degenerate t-structure such as (U,0). In the last case the actual lower bound forces K=0, so the theorem remains true. In the standard case both positive and negative q put H^q(E) in degree q before shift and in degree zero afterwards. Every step is below 2000 characters; the only intermediate comparisons are the explicitly written elementary adjunction and good-truncation calculations.
