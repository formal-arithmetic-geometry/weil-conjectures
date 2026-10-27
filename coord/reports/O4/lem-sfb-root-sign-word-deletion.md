## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-root-sign-word-deletion.json`: item split into five explicit elementary steps; statement and statement dependencies unchanged; no Mathlib match.
- `citations.json`: `[]`, since every proof step is a calculation or finite sign argument from the item's hypotheses and no step cites another node.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. Mathlib leaves: 0. No attachments.

WANTED: J. E. Humphreys, *Reflection Groups and Coxeter Groups* (1990), §1.8, the reference Milne C.10 gives for simple transitivity, for `lem-sfb-root-sign-word-deletion`. No Humphreys document was found in the named literature directory or its list. The proof here is explicitly agent-written; it does not claim to reproduce that unavailable proof.

The item arrived with no proof. Its statement is true as written and is retained: neither finiteness, spanning, crystallographic integrality, nor a Coxeter presentation enters the calculation. The inherited blueprint ancestor is null (confirmed by `blueprint_refs.py ancestor`); its existing `from.place` and `via` chain are preserved. The actual newest blueprint direct-images proof paragraph (3) was read: it contains the distant direct-image route, not a sign-change lemma. The local purpose is precisely the exchange input used in step 10 of `lem-sfb-root-chamber-simple-transitivity`.

Nothing remains unfinished in the split. No Lean was written or compiled, and no repository file was changed.

## Searches and reuse

Project-source searches over `lean/WeilConjectures/` for the item id, reflection, root signs and word deletion found no declaration stating the item. Hence there is no attachment. Searches of the whole DAG for sign-change deletion, positive/negative root words and orthogonal reflection words located this item and its chamber parent but no replacement. The parent uses this item, so citing the parent would be circular. Blueprint-wide `reflection` found only the unrelated Fourier-inversion node; `deletion` and `sign-change` found none. No new node was needed, so no duplicate pairs arise.

I retained the inherited search records and added only the actual recorded searches made for O4. LeanSearch and LeanFinder were each tried with two phrasings; Loogle searched `"exchange"`, and the logged Mathlib grep searched `exchange|deletion|wordProd_mul_getD_rightInvSeq` in `GroupTheory/Coxeter`. The search hits were read. In particular, `CoxeterSystem.wordProd_mul_getD_rightInvSeq` at `Mathlib/GroupTheory/Coxeter/Inversion.lean:349` assumes `cs : CoxeterSystem M W`, as the file's opening explains. Constructing that presentation from the current hypotheses is not a one-line specialization and would reverse the use of this lemma in chamber freeness. The RootPairing base induction/reflection results (including `Base.lean:639`) require a crystallographic reduced finite root pairing and a base; our hypotheses give only sets of vectors with a sign partition. These are not matches. No search service failure was recast as absence.

## Review by O4

I read Milne, *Algebraic Groups*, Appendix C.8--C.10 and C.19--C.22 (printed pp.609--612, PDF pp.621--624). C.10 states simple transitivity but refers its proof to Humphreys §1.8. Accordingly the new proof is labelled agent-written: it supplies the concrete exchange calculation required by the chamber parent's freeness argument, rather than citing C.10 as a proof of its prerequisite. I also read the chapter and unit records, the current blueprint direct-images paragraph (3), the chamber parent's statement and proof, and the existing dimension definition. No new node requires a separate source check.

For step 1, the only inputs are the formula in the item, symmetry and bilinearity, and positive definiteness. I checked the denominator is positive for each nonzero vector, that pairing the reflected vector with its root changes that pairing's sign, and that the two negative cross terms in the form expansion cancel the positive quadratic term. This proves involutivity, linearity and preservation of the form directly. No theorem about abstract reflections is silently used.

For step 2, the identity `q s_b = s_(qb) q` is written pointwise, not asserted as an unexplained conjugation. Form preservation from step 1 makes both numerator and denominator agree. In particular `qb` is nonzero because its squared length equals the positive squared length of `b`. This needs no inverse, group presentation or root-pairing comparison. There are no cited node statements in either step.

For step 3, the partition is disjoint, and preservation of R places every suffix image in exactly one of its two parts. I checked the indexing with rightmost-first composition: `c_i = s_(a_i) c_(i+1)`. The largest negative suffix index exists in the finite nonempty set containing 1, while `c_(k+1)=b` is positive. Its successor is therefore positive. Only this finite list is used; R itself may be infinite. The empty word is excluded by the given negative-image hypothesis, not by an added length assumption.

For step 4, the precise hypothesis used is the image equality on `P` minus the singleton `a_j`. Its inclusion direction already suffices: a positive `c_(j+1)` other than `a_j` would have a positive image, contradicting the chosen negative image. Thus `q b = a_j` is forced. This is a direct use of an assumption in the item's own statement, not of a definition node or a hidden root-system theorem.

For step 5, I checked the product order explicitly: `w = p s_(a_j) q`, and step 2 puts `q s_b = s_(a_j) q`. Multiplication and `s_(a_j)^2=1` cancel the two adjacent factors, giving exactly the required word with index j omitted. Empty prefix and suffix cause no change. Every step has `uses: []`, so C4 has no external citations to quote; the empty citations file is deliberate. All steps are below 2000 characters and contain the actual calculations, not a deferred standard lemma.

I tested k=0 (negative image impossible), k=1 (the sign change forces b=a_1 and both sides are the identity), and repeated letters in rank one (odd words delete to the even identity word; even words never trigger the hypothesis). In type A2 with simple roots a,c, the word s_a s_c gives j=2 for b=c and j=1 for b=a+c; these test both empty-suffix and empty-prefix cases and confirm the product orientation. When V=0, R and P are empty and there is no b; when D is empty, only the empty word exists. None of these requires excluding an edge case.

Against delivery-errors B--E: there are no new nodes to inflate the DAG, no restatement moved into a child, no missing non-elementary fact, no node cited beyond its statement, and no changed mathematical assertion. The general reflection intertwining calculation is only a few lines of substitution and remains a step under the explicit elementary-fact rule. The finite sign selection and final cancellation are equally elementary. The source's missing exchange detail has been supplied instead of assumed. I corrected the initially absent proof and completed its search and blueprint audit; there was no statement dispute to repair.
