# Stage-1 report: lem-trf-simplicial-abelian-descending-correction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-simplicial-abelian-descending-correction.json — existing statement, split; statement and statement dependencies unchanged.
- dag/nodes/sec-trace-formula/lem-trf-simplicial-mixed-face-degeneracy-identities.json — statement, Mathlib leaf; four mixed-identity cases, supplied by four declarations in SimplicialObject/Basic.lean.
- citations.json — verbatim statement quotations for each cited node in each proof step.
- searches.jsonl — unmodified search-command log.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and descending-correction names, and inspected concept searches; no project declaration states the item. A Mathlib declaration is recorded only as a leaf, not an attachment.

## Literature wanted

None.

## Audit findings and changes

The imported statement is correct and remains unchanged. Its empty proof is now an explicit descending induction, exposing the calculations hidden by the words “A simple calculation” in Stacks 08NZ (lemma-simplicial-group-kan), third proof paragraph. The lower defect uses the pair (i,r) in the horn compatibility condition, and the upper defect uses (r,i). Both indices differ from the missing face k in each use. No property of the missing face is asserted or required.

The existing definition node gives the operators but does not assert mixed identities. I therefore did not cite that definition for the mixed theorem. The face-face identity already has a Mathlib leaf, lem-weil-pbc-simplex-face-face-identity; applying the contravariant functor to it is an elementary first step. The new mixed-identity leaf gives all the relations needed for degeneracy corrections, without assuming any Kan condition or any comonad presentation. It is strictly smaller than the item: it says nothing about compatible prescribed faces, a recursion, defects, or induction.

Mathlib search results were read. HigherFacesVanish.induction in DoldKan/Faces.lean:160 is about eliminating upper faces of a morphism with zero targets; it does not state the item with its arbitrary prescribed faces and lower-face preservation. The mixed identities in SimplicialObject/Basic.lean:149,156,168,186 match the new leaf exactly, one declaration per case. The leaf search includes LeanFinder, Loogle, LeanSearch and grep, with queries and actual results copied from searches.jsonl; the separate grep for of_gt records line 186. The item also has a second semantic phrasing, and the earlier searches inherited from its creation are preserved. No compiler or Lake command was run.

The chapter and unit records were read. The current latest blueprint's sk-i-curve-zero and lem-trf-local-term-locality proof were read as the ancestor context; the generic simplicial calculation is reached through the inherited from/via chain, not a change to a chapter or unit route. Searches of the whole blueprint for simplicial identities, descending, face degeneracy and mixed simplicial found no node giving the new mixed-identity result. DAG title, statement, 0167 and declaration-name searches were also read. Reconstruction and word-presentation nodes assume mixed identities rather than prove that the operators of an arbitrary simplicial object satisfy them. Comonad identities require extra presentation data, so are not a more general result of which this is a specialization.

The first delivery dry run required the singular `mathlib_match.line` field in addition to the supplied `lines` list. I added line 149, retaining the complete per-clause lines and explanations. No mathematical change was needed.

## Unfinished work

None in this one-level split. The new dependency is a Mathlib leaf, with no postponed proof and no new unsplit nodes.

## Review by Q38

I read Stacks simplicial.tex, lemma-simplicial-group-kan (08NZ), including its initial horn compatibility equations and both induction paragraphs. The item's descending recursion is the additive version of its third paragraph with the source's progress parameter replaced by the descending face index r. I also read lemma-relations-face-degeneracy (0167), parts (1)--(4), and the pinned Mathlib identities at Basic.lean:115--190. Contravariance reverses the order of composition, exactly as in those declarations.

Step 1 uses the statements of def-weil-pbc-simplicial-object and lem-weil-pbc-simplex-face-face-identity: the former really defines d_i as G(delta_i), and the latter really states the required equality of delta composites. Applying G gives the face identity; homomorphism additivity comes from taking values in Ab. Step 2 sets the complete induction invariant and proves its base directly from the given v. Step 3 uses only that invariant, the original compatibility hypotheses and Step 1; I checked the displayed lower and upper equalities separately rather than interchanging their indices informally.

Step 4 uses the statement of the new mixed leaf, not its proof. For the lower range i<k<r one has i<r-1, precisely the strict inequality required by the first mixed case. When that range is nonempty r>=2, so s_(r-2) exists. In the upper range i>r, the required condition is i>(r-1)+1; the defect has the shifted vanishing d_(i-1)b_r=0 established in Step 3. The adjacent identity has degeneracy index r-1 and gives d_r s_(r-1)=id, including r=1. Step 5 applies additivity and cancellation in an abelian group to prove the successor invariant, and Step 6 checks the empty ranges at k=n and k=0. These steps hide no lifting or exactness lemma.

I tested n=2 with each k=0,1,2. For k=1 the only correction is r=2 and preserves face 0 by s_0 d_0 b_2=0. For k=0, the r=2 step fixes face 2, and the r=1 step preserves it by d_2 s_0=s_0 d_1, with d_1 b_1=0. For k=2 no correction occurs. I also checked constant simplicial abelian groups: compatibility forces the given faces to agree and the first nontrivial correction produces that common element. The zero simplicial group is immediate. Every face of b_r lies in a nonnegative degree because n>=2. The new leaf's n=1 case asserts only the two adjacent identities; its nonadjacent formulas start at n=2, so no negative degree appears there either.

Against delivery-errors B--E: the leaf is self-contained, has no proof or proof sketch, cites the actual operator definition, names the correct Stacks tag/label and exact Mathlib lines, and has authentic logged searches. Existing source-tag neighbours are distinguished below. Every non-elementary external identity is a cited statement, quoted verbatim in citations.json; no definition is being used as an unstated theorem. The split carries the actual induction rather than replacing its clauses by new nodes. All steps are elementary applications of the displayed identities, the stated compatibility and the preceding induction steps, and each is under 500 characters. I checked there is no dependency back to the item through the new Mathlib leaf. No statement dispute, source error or forbidden SGA citation was found.

## Not duplicates

lem-trf-simplicial-mixed-face-degeneracy-identities vs def-weil-pbc-simplicial-object: the existing node states “Simplicial objects of a category, face and degeneracy maps”; the new leaf states mixed face-degeneracy equations for an arbitrary simplicial object. It does not state that existing result.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-weil-pbc-simplex-face-face-identity: the existing node states “First cosimplicial identity for the face maps of the simplex category”; the new leaf states mixed face-degeneracy equations for an arbitrary simplicial object. It does not state that existing result.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-weil-pbc-simplicial-matching-object: the existing node states “Matching objects of a simplicial object in a category with finite limits”; the new leaf states mixed face-degeneracy equations for an arbitrary simplicial object. It does not state that existing result.

lem-trf-simplicial-mixed-face-degeneracy-identities vs def-sfb-pure-coface-word: the existing node states “Raw pure coface words and contextual coface replacements”; the new leaf states mixed face-degeneracy equations for an arbitrary simplicial object. It does not state that existing result.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-sfb-pure-codegeneracy-word-relations: the existing node states “Completeness of pure codegeneracy word relations within the endpoint degrees”; the new leaf states mixed face-degeneracy equations for an arbitrary simplicial object. It does not state that existing result.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-sfb-pure-coface-word-relations: the existing node states “Completeness of pure coface word relations within the endpoint degrees”; the new leaf states mixed face-degeneracy equations for an arbitrary simplicial object. It does not state that existing result.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-trf-comonad-mixed-degeneracy-identities: the existing node proves identities for explicit powers of an endofunctor with counit and comultiplication; the new leaf concerns every simplicial object, without any such presentation.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-trf-simplicial-operators-reconstruction: the existing node assumes the mixed relations to construct a simplicial functor; the new leaf deduces mixed relations from an already given simplicial functor.

lem-trf-simplicial-mixed-face-degeneracy-identities vs lem-sc-module-cup-godement-simplex-presentation-faithful: the existing node asserts faithfulness of a generators-and-relations category functor; the new leaf only gives the mixed equations on arbitrary simplicial objects.
