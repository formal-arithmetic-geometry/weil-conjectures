# Stage-1 report: lem-sfb-root-length-inversion-count

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-root-length-inversion-count.json`: statement, split; no Mathlib match. Five proof steps, reusing the existing reviewed deletion lemma. Statement and statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for the only node citation, step 3.
- `report.md`: this report. `searches.jsonl` contains the actual Q87 search log.

New nodes: 0. New Mathlib leaves: 0. Local scratch work comprises a Milne text extraction, the JSON-writing script, and `check_small_cases.py`; these are not delivery nodes or Lean files.

## Attachments

None. Searched all of `lean/WeilConjectures/` for the exact blueprint id and for inversion, Weyl/Coxeter, root-length and length/cardinality vocabulary. There is no project declaration giving this statement. Mathlib search hits are not project attachments.

## Wanted literature

WANTED: Björner--Brenti, *Combinatorics of Coxeter Groups*, Lemma 4.4.3 and Proposition 4.4.4, printed pp.102--104 (PDF pp.110--112), for lem-sfb-root-length-inversion-count. The local PDF named by the existing source field is absent. I read those pages online from the existing university-hosted source URL: https://sites.math.washington.edu/~billey/classes/reflection.groups/references/EntireBook.pdf . No document was downloaded into the repository. The available Milne iAG2017 Appendix C.8--C.11 supplies the finite real-root setup, not a proof of the length formula. Accordingly proof_origin is agent: the argument explicitly adapts the sign-permutation and inversion-set induction to the unnormalized real roots of this item.

## Findings and corrections

The item was unsplit, with no proof, no existing sandbox split, and no repair note. I kept its statement exactly. The only non-elementary input needed is already stated by `lem-sfb-root-sign-word-deletion`, in this same unit. Its statement is more general than needed, and has neither a word-length conclusion nor an inversion-count conclusion. The item's new steps supply the root-coordinate sign check, the reduced-prefix argument, the cardinality recurrence and the induction. No new node was needed.

I retained all inherited source, created, blueprint and search records, then added the queries actually run by Q87. I read the search results and source of CoxeterSystem.length (Length.lean:75), IsReduced (81), exists_isReduced (85), length_rightInvSeq (Inversion.lean:246), RootPositiveForm.rootLength (RootPositive.lean:171), and Base.IsPos.reflectionPerm (Base.lean:578). Minimal abstract Coxeter length and the length of an inversion *list* do not count roots. rootLength is a squared norm. Constructing a Coxeter system or a RootPairing base for the raw data is not a one-line specialization. Both semantic phrasings, Loogle, LeanSearch and the recorded source searches found no match for the item.

The current blueprint is latest/main-20261024 (ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its unit and direct-image proof. Latest direct-image step (3) uses proper image, open image and compactification; the item's long from.place is inherited provenance for the auxiliary alteration/moduli/flag chain, not a claim that the latest proof itself contains that whole chain. blueprint_refs ancestor reports null for this created chain, as already on live; I retained that metadata rather than inventing an imported ancestor. No chapter or unit file was changed.

## Not duplicates

No new nodes. The prospective exchange input was found as the existing `lem-sfb-root-sign-word-deletion` and reused. Whole-DAG searches for exchange/deletion, positive roots and root length, plus blueprint_refs searches for inversion, positive roots, exchange condition and word length, found no imported blueprint node stating this length formula. I also searched the latest blueprint text. The chamber-transitivity statement describes a simply transitive action; it does not state this numerical length formula. The item itself already is the appropriate node.

## Unfinished work

None within this stage-1 split. The proof is a natural-language DAG proof, not a Lean implementation. No Lean was written and no compiler, Lake or build command was run.

## Review by Q87

I read Milne Appendix C.8--C.11 from the local PDF, and Björner--Brenti Lemma 4.4.3 and the full proof of Proposition 4.4.4 online. Milne's C.10 only refers elsewhere for its proof, so I did not use it as an unstated exchange theorem. I opened the entire existing deletion node, including its statement, source and proof, and checked the existing dimension definition against the item's only statement dependency. There are no new-node sources to review.

For step 1 I checked that the reducedness assumption includes the negative of every root, that the sign partition is disjoint because roots are nonzero, and that the displayed reflection formula gives an involution. Thus every element of the *generated subgroup*, rather than an assumed Coxeter presentation, has a word whose length can be minimized. All of this is elementary from the stated objects.

For step 2 the essential hypothesis is reducedness: a positive root distinct from a simple root cannot lie on its line. It therefore has a positive coordinate away from that simple root. Reflection leaves that coordinate unchanged, so the sign hypothesis forces the image positive. Involutivity proves equality of sets. This is the actual coordinate proof behind Lemma 4.4.3, not an uncited theorem invoked by name; it is a short elementary step and does not merit a node.

Step 3 is the only step with a node citation. I read the statement of `lem-sfb-root-sign-word-deletion` and verified the substitution R=Phi, P=Phi+, D=Delta, word=the prefix u, b=the final simple root a. Step 1 gives the disjoint sign partition and the reflection formula, the item's assumptions give permutation of R, and step 2 gives the required equality on P minus the simple root. The cited statement says that u s_a deletes one letter when u a is negative, and explicitly forces the prefix to be nonempty. That clause handles n=1 without treating n-2 as a negative word length. The prefix is reduced by the explicit replacement argument, and deleting from it contradicts minimality of the whole word. The citation quote in citations.json is copied verbatim from that exact statement. I use no construction hidden in the cited proof.

For step 4 I checked both directions of the inversion-set equivalence, the orientation w=u s_a, and disjointness: a is not inverted by u, reflection is a permutation on P minus a, and a is inverted by w. The resulting bijection adds exactly one root. Finite cardinality is justified by the finite root set. The induction has its base in step 3 and induction step in step 4; it assumes the formula only for the strictly shorter prefix. Step 5 handles V=0 directly. These last steps are elementary assembly, not extra unquoted geometric or Coxeter facts.

Against delivery-errors B--E: all objects are introduced, no new unsplit node contains a proof, no Stacks tag is being substituted for a definition, and TeX is singly escaped after JSON decoding. There is no relevant Stacks result used here: the sources are the explicitly identified root-system texts. The non-elementary input is a cited statement with all hypotheses checked; elementary facts are written out. Nothing was moved into a renamed copy of the item, and no cycle is introduced: the deletion node has no proof dependencies and only the dimension statement dependency. No off-unit tool use or SGA route is used. All five steps are under 2000 characters.

I independently enumerated the actual integer reflection matrices in rank zero, A1, A1 x A1, A2, B2 and G2, using breadth-first word lengths. For all 33 group elements the inversion count equals that minimum. For every simple reflection I also checked permutation of the other positive roots and, whenever u a is positive, I(u s_a)=s_a(I(u)) disjoint union {a}. Root counts were respectively 0, 2, 4, 6, 8 and 12; maximal lengths were 0, 1, 2, 3, 4 and 6. This tests the empty case, disconnected case, unequal root lengths, and the multiplication orientation. These computations corroborate the proof, whose argument applies to all systems satisfying the hypotheses.
