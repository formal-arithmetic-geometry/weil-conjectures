# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-adjunction-square-shift-mate.json`: statement; five-step split; Mathlib searches found ingredients but no match for the full four-category statement with its two explicit adjunct formulas.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `report.md`: this report.

No new DAG nodes; no new Mathlib leaves. The existing statement, source, statement dependencies, created record and blueprint provenance were retained. The new logged searches were appended without removing the inherited searches.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for the adjunction square, mate and shift notions. `CategoryTheory.adjunctionSquareComposition` in `CategoryTheory/AdjunctionSquareComposition.lean` concerns invertible pasting squares and assumes additional adjunctions; it does not state this item. The geometric `mvCanonicalBaseChange_shift` is a specialization with pinned derived data and does not supply all clauses here. No exact project declaration was found.

## WANTED

None. The sources read are locally available.

## Problems found and corrected

The item was unsplit with an empty proof. Its statement was well typed and did not require a dispute or a change. In particular the second adjunct uses the inverse of the primed right-adjoint shift; reversing that inverse would be ill typed. The Stacks source itself does not state the four-category refinement, and the new proof is marked agent-written. No proof is attributed verbatim to Stacks beyond the actual adjunction and shift constructions cited.

## Unfinished work

None for this one-level stage-1 split. No Lean was written or compiled. No repository or launcher file was edited.

## Not duplicates

No new nodes were created. Whole-blueprint searches for `adjunction shift`, `mate`, and `shift compatible`, and whole-DAG title/statement searches for adjoints, mates and shifts, were considered. The existing `lem-weil-pbc-formal-exact-projection-mate` assumes tensor and triangulated data; `lem-weil-pbc-tensor-arrow-mate-naturality-shifts` is a tensor-arrow statement in two categories; `lem-pc-pinned-base-change-mate-shifts` concerns schemes with selected derived comparisons. None states the present general four-category result and its two adjunct formulas. No duplicate node was introduced for any of these specializations or for an elementary naturality calculation.

## Review by NL

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three levels in `SETUP.md`, `GOAL.md`, the chapter and unit records, and both occurrences of delivery-errors B through E. The unit route and chapter were retained. The nearest blueprint ancestor is `lemma-weil-pbc-perfect-projection-formula`. I read its current main-20261015 proof, especially the first paragraph's closure under shifts. This item supplies a formal comparison calculation below that paragraph, rather than replacing the unit's route.

For the mathematical source I read `literature/stacks-project/derived.tex`, Tag 0A8D (`lemma-adjoint-is-exact`), the first paragraph constructing the shift comparison by adjunction and the ensuing naturality calculation, and `categories.tex`, Tag 0037 (`definition-adjoint` and the paragraph after it). The former works with triangulated categories but its adjunction calculation motivates the formal argument here; no triangulated theorem is applied to the bare shifted categories. The latter explicitly gives natural bijections and both formulas for adjuncts. There are no new nodes needing separate sources.

I opened and read the statement of every cited DAG node. `lem-weil-pbc-commshift-nattrans-comp-whisker` supplies the composite comparison convention; `lem-weil-pbc-adjunction-of-natural-bijection` actually includes the bijection's two naturality laws, both unit/counit formulas, and triangle identities; `lem-weil-pbc-adjunction-shift-compatibility-unique` actually states clause (i), compatibility with the counit from compatibility with the unit. All three are existing Mathlib leaves, so their use from another unit needs no route exception. I also read `Mathlib/CategoryTheory/Shift/Adjunction.lean` lines 64–145, `Adjunction/Basic.lean` lines 160–182, and `Shift/CommShift.lean` lines 406–425 to compare the search hits with those statements. The newly logged searches, including a second semantic phrasing and a second Loogle pattern, returned only these ingredients or definitions that already assume a shift-compatible transformation. Nothing returned the entire item as a one-line specialization.

Step 1 uses the cited composite convention and then writes every equality. The critical naturality square for beta is at `a_P : L(P[n]) -> (LP)[n]`, so its source is not silently replaced by `LP[n]`. The shift equation is then applied at `E=LP`. The unprimed unit hypothesis replaces `b_LP R(a_P) eta_(P[n])` by `eta_P[n]`, and naturality of c moves `r(eta_P[n])` across c. These are functor/naturality identities under the exact stated hypotheses. I marked this substitution calculation elementary, with its full expansion present.

Step 2 uses the existing adjunction node's forward and inverse hom formulas, with `F=L'`, `G=R'`, `X=rP`, `Y=B=tLP`. Consequently theta is the inverse image of h and the bijection is injective. The same assertion at `P[n]` has target `tL(P[n])`, not `B[n]`. This is why the postcomposition d is kept in Step 3. Step 3 uses the exact target-naturality law in the adjunction node, giving `Phi(d theta)=R'(d) h` for source `r(P[n])` and target `B[n]`. This is a direct specialization, hence elementary.

Step 4 uses clause (i) of the shift-compatibility node, not its uniqueness clause or its proof. Its hypotheses hold because the primed unit equation is explicitly assumed, and both a' and b' are natural isomorphisms. It gives `eps'_(B[n]) = eps'_B[n] a'_(R'B) L'(b'_B)`. I then compute the inverse hom image of `q=(b'_B)^(-1) h_P[n] c_P` using the adjunction node. The adjacent images of b' and its inverse cancel. Naturality of a' at `h_P:rP -> R'B` is written as the next equality, and functoriality of [n] gives the shifted theta formula. Thus the second adjunct identity is proved without treating it as a new black box or restating it as a child node. This step is marked non-elementary for its use of unit-to-counit compatibility.

Step 5 cancels only the isomorphism b', obtaining equality of the two adjuncts from Step 1, and uses the same hom-bijection's injectivity. There is no assumed inverse of beta or theta and no adjunction for r or t. Each assertion is for an arbitrary fixed n, so the proof covers zero and negative shifts without invoking strict commutation or an unproved iteration argument.

For edge cases I checked the identity square with identity shift comparisons: the h-square becomes the given beta shift equation and the adjunct calculations reduce to the unit/counit triangle formulas. For all four categories equal to vector spaces with trivial shifts and L=R=L'=R'=r=t=Id, a scalar beta (including beta=0) gives h=theta=beta and all three equations hold; this explicitly checks that no invertibility of beta entered. Nontrivial natural shift comparisons are kept in every line; the typed map q goes from r(P[n]) through (rP)[n] and (R'B)[n] to R'(B[n]). Empty categories give vacuous assertions. No size restriction, exactness, additive or tensor hypothesis was used.

Against delivery-errors B–E: there are no new node forms or fabricated search records, the existing statement is self-contained and has been retained, every non-elementary ingredient is one of the three cited statements, every quotation in citations.json was tested as a literal substring of its source statement, and proof_deps is the exact union of uses. No argument uses another node's proof. The source's omitted details are precisely the displayed calculations here. No clause was moved into a new node, and the proof depends only on existing Mathlib leaves, so it introduces no dependency cycle. Every step is under 1000 characters; none hides a long auxiliary comparison lemma. I checked objects and hypotheses at each substitution and found no source error requiring a statement dispute.
