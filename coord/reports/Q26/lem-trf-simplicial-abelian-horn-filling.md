## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-simplicial-abelian-horn-filling.json`: statement node, split; original statement retained verbatim. Seven explicit steps follow the additive specialization of Stacks 08NZ.
- `citations.json`: one verbatim statement quotation for every node cited by every step.
- `searches.jsonl`: six actual searches run by msearch.py; their returned records were read and added to the item's existing searches.
- `report.md`: this report and signed review.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: `def-weil-pbc-simplicial-object` and `lem-weil-pbc-simplex-face-face-identity`.

Attachments: none. Searches of `lean/WeilConjectures/` for the blueprint tag and for horns, Kan complexes, compatible faces and simplicial abelian groups found no declaration stating this theorem. The Čech cosimplicial abelian groups in the hits have a different purpose and statement.

WANTED: none. All mathematical sources used are present in `literature/stacks-project/simplicial.tex`.

The original node was statement-only, with no proposed proof to preserve. Its statement agrees with the compatible-face formulation in the first paragraph of Stacks 08NZ's proof. There is no statement dispute or source error. The parent and other 08NZ hits were opened: the boundary-lifting nodes concern surjective quasi-isomorphisms between two simplicial abelian groups (08P1); the Dold–Kan nodes concern normalization and realized homotopy. None supplies the current compatible-face filler statement directly without additional mathematics. No parent or duplicate is cited as a replacement for the item.

The source's two phrases “An easy calculation” and “A simple calculation” have been replaced by the actual face calculations in Steps 3, 5 and 6. The source starts its lower induction at s_0(a_0); the equivalent zero-start induction here includes that case as its first correction and also covers k=0 uniformly. The separate n=1 argument avoids writing d_i on degree-zero elements.

Nothing remains unfinished in this one-level split. The required dry run and push are performed after this report is written; this report does not pre-assert their result.

## Searches and reuse

The six msearch calls are recorded verbatim in searches.jsonl: one LeanSearch, one Loogle, two LeanFinder phrasings, and two greps. The first semantic results give KanComplex.hornFilling, which assumes the property to be proved. I read Mathlib/AlgebraicTopology/SimplicialSet/KanComplex.lean lines 35–60: both hornFilling (44) and exists_lift_of_kanComplex (55) require [KanComplex]. The Loogle results give Kan extensions and Dold–Kan reflection of isomorphisms. The second phrasing gives faces of pointed-simplex multiplication structures, which assume that structure and do not fill arbitrary group horns. Grep supplies Dold–Kan files and conditional Kan filler lemmas, not an instance or theorem for arbitrary simplicial abelian groups. No unavailable service was recorded as a negative result. The five historical searches in the repository node are retained with their dates.

Whole-DAG searches used the tag 08NZ and the phrases face/degeneracy, simplicial identities and horn filling; the existing simplex-face-face-identity node was opened in full. Whole-blueprint searches with tools/blueprint_refs.py used “simplicial”, “horn”, “face degeneracy”, “compatible faces” and “Kan complex”. No blueprint node states the item. The ancestor command gives lem-trf-local-term-locality; its current main-20261015 text, the inherited blueprint support chain, dag/chapters/sec-trace-formula.json and dag/units/sk-i-curve-zero.json were read. This item is an auxiliary input, not the unit's key statement, so no unit realization fields are changed.

## Not duplicates

No new nodes are created. Mixed identities of Stacks 0167(2)–(4) are verified by direct evaluation of the defining order maps in Step 1; they do not become unnecessary statement nodes. The already existing 0167(1) face-face identity is cited, rather than recreated. The two cited leaves are generic simplicial notions and combinatorial tools, so their use does not replace the unit's route.

## Review by Q26

I read the statement and entire proof of Stacks Tag 08NZ (simplicial.tex, lemma-simplicial-group-kan, lines 5755–5803), and Tag 0167 (lemma-relations-face-degeneracy), including the actual definitions of the cofaces and codegeneracies preceding it. The item is exactly the abelian specialization of the compatible-face problem posed at the start of 08NZ. In particular n is positive, k may be either endpoint, every prescribed a_i lies in G_{n-1}, and compatibility is asserted only for pairs of prescribed indices. The statement was not weakened. There are no new statements to audit against a source.

For Step 1 I opened both cited statements. The simplicial-object node defines a contravariant functor and explicitly defines cofaces as injections omitting an index and codegeneracies as surjections repeating an index. It does not assert the mixed identities, so the proof does not pretend it does: the indicator formulas evaluate the two composites on every element and prove their equality, then apply functoriality. I checked each of the cases i<j, i=j, i=j+1 and i>j+1, including the threshold equality. The face-face node states precisely the equality of the two coface composites; applying G yields precisely the face identity used. Thus neither citation uses a theorem hidden in a cited proof.

Step 2 uses only the cited definition and Step 1's two cancellation identities: for n=1 either possible prescribed face of s_0(a_i) is a_i. There are no compatibility equations and no maps G_0 to a negative degree.

Step 3 cites the simplicial-object definition and the face-face identity, with their meanings as just checked. I verified the invariant before and after each lower correction, computed d_i(a_r-d_r(v_r)) using exactly the hypothesis for the pair i<r<k, and checked that r<k<=n permits s_r. At r=0 there are no lower indices, so the displayed formula with r-1 is never instantiated. This is an explicit two-line calculation plus finite induction, not an uncited filler theorem.

Step 4 uses only the cited simplicial-object definition and the earlier lower induction. It states the descending invariant, its base w_n and the correction w_{r-1}; r>k>=0 guarantees r>=1, so s_{r-1} is defined. Its claim about the transition is proved in the next two steps, rather than assumed to initialize an induction circularly.

Step 5 uses the two cited statements to expand the lower-face error. Every occurrence of a_i or a_r is allowed, since i<k<r excludes the missing index. The inequality i<k<=r-1 puts d_i s_{r-1} in the first mixed case. If there is a lower index at all, r>=2, so s_{r-2} is defined. Hence the lower invariant survives without a hidden endpoint exception.

Step 6 again uses the cited definition and face-face equality, now with r<i. I checked the compatibility equation in its required direction d_{i-1}a_r=d_r a_i, and the face equation d_{i-1}d_r=d_r d_i. This makes the error zero on the preserved upper faces. The mixed identity for i>r and the identity d_r s_{r-1}=1 prove, respectively, preservation and the newly set face. All operators are homomorphisms because G has values in abelian groups; no flatness, exactness, topological realization or Dold–Kan theorem is used.

Step 7 reads the invariant at r=k. At k=n the descending sweep is empty; at k=0 all lower-face conditions are empty. I also checked n=2 for k=0,1,2: each sweep uses only s_0 or s_1, and the only face-comparison calculations land in G_0. For a constant simplicial abelian group, compatibility for n>=2 forces all prescribed faces equal, and the algorithm gives that common element; for n=1 it gives the sole prescribed element. For the zero simplicial group every correction is zero. No property of the missing face a_k is assumed, and that symbol is never introduced.

Against delivery-errors B–E: the node is self-contained, existing metadata and the original statement are retained, the two references are definitions/results with exactly the stated content, quotations were copied verbatim, there are no new nodes restating clauses, and every omitted calculation in 08NZ is supplied in the item's own steps. Each step is marked elementary because its argument is explicitly a defining-map evaluation, an additive identity, or a finite induction using those displayed identities; the tag alone is never used in place of a proof. No step exceeds 2000 characters (the longest is 1094). I corrected the potential degree-zero and negative-index ambiguity by treating n=1 first and explicitly restricting formulas with r-1 or r-2 to nonempty index ranges. No mathematical statement, source route, or launcher tool was changed.
