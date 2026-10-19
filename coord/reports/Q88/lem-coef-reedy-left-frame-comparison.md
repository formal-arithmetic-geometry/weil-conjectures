# Stage-1 report: lem-coef-reedy-left-frame-comparison

## Files written

- dag/nodes/sec-six-functors/lem-coef-reedy-left-frame-comparison.json: statement, split; no complete Mathlib match. Four proof steps reuse three existing nodes.
- citations.json: six step/node citations, each with a verbatim excerpt from the cited statement.
- searches.jsonl: actual searches made by the prescribed msearch command; retained as search evidence.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged. No Lean files, compilers, project tools or shared files were modified.

## Attachments

None. Searches for the exact blueprint tag and for Reedy, Quillen and cosimplicial-frame terminology under /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no project declaration stating this item. The upstream master checkout was treated only as reference material, not as proof evidence.

## Wanted literature

WANTED: Mark Hovey, Model Categories, Lemma 1.1.12 (printed pp. 6-7), Theorem 5.2.5, Theorem 5.2.8 (p. 128), and Lemma 5.5.1 (p. 133), for lem-coef-reedy-left-frame-comparison: a locally archived copy in literature/. The source URL already recorded on the item is readable online, and I read these places there. I did not download it or change literature/LIST.md. The proof is explicitly marked agent-written and gives the full argument from existing cited statements, rather than claiming to follow a locally held document.

## Findings and changes

The original statement is correct, and no STATEMENT-DISPUTED correction is needed. Its source points to the right lifting argument but does not yet give a split. Proposition 5.4.7 concerns mapping complexes; this particular comparison only needs the model lifting axiom once transported Reedy cofibrancy is established. The source's relative degree-zero construction is unnecessary under the stronger cofibrancy and identity-augmentation hypotheses present here: lifting out of the initial diagram suffices, and the equation over the constant object forces degree zero to be the identity. This stays below the unit's route and changes neither its statement nor its proof route.

I read the chapter and unit records, the current main-20261015 proof paragraph 2 of prop-coef-integral-exceptional-adjoint, the parent cosimplicial-frame-mapping steps, and the inherited blueprint ancestry. The item supplies the left-Quillen frame comparison used in parent step 13. Searches of the entire DAG and blueprint for Reedy, cosimplicial, frame and Quillen terminology produced no blueprint duplicate. The related simplicial-frame-comparison node has a coaugmentation and a lift into a Reedy fibrant target, so it does not replace this item. The parent frame-mapping theorem depends on this item and cannot be used as a black box here.

The existing leaf lem-coef-brown-split-factorizations states exactly the split factorization needed for the Brown argument. The existing leaf lem-weil-pbc-left-adjoint-preserves-colimits states the general colimit preservation result, including the canonical isomorphism. Reusing these avoids both duplicate nodes and new nodes merely stating elementary consequences. No new unsplit lemma was needed.

## Review by Q88

I checked delivery-errors B through E against the actual node and its cited statements. There are no new nodes to audit, no added hypotheses, no restatement of a clause as a new child, and no use of a node's internal proof instead of its statement. All the non-elementary foundations are cited existing statements. Every proof step is fewer than 900 characters; no step longer than 2000 characters hides an additional lemma.

For step 1 I opened the entire statement of lem-weil-pbc-left-adjoint-preserves-colimits and checked Stacks 0038, categories.tex, lemma-adjoint-exact, part (1), and Mathlib/CategoryTheory/Adjunction/Limits.lean:90-99. It says that the image colimit cocone is universal, and identifies the canonical comparison as an isomorphism. I apply this only to the small latching categories, and also to the empty category in degree zero. I read lem-coef-reedy-model-structure's statement: its latching criterion gives precisely the remaining cofibrations. Agreement on coprojections identifies the actual latching map, not just the two objects. Invariance under the comparison isomorphism is justified by transporting lifting squares. Thus the step proves cofibrancy of TS without assuming that T preserves matching limits.

For step 2 I read the full statement of lem-coef-brown-split-factorizations, and its Mathlib CofibrantBrownFactorization structure and existence instance at BrownLemma.lean:48-53,85-87. The hypotheses require both endpoints of f to be cofibrant; the step states exactly that. Its factorization supplies qi=f and qs=1 with i,s cofibrations and q a weak equivalence. The two-out-of-three axiom is stated in lem-coef-reedy-model-structure. These equations first make i,s trivial cofibrations and then make Tq and Tf weak equivalences. No preservation of q as a fibration, and no fibrancy of either endpoint, is used. This is a few applications of the cited statements, rather than an uncited appeal to Brown's lemma.

For step 3 I checked that lem-coef-reedy-model-structure explicitly says Reedy cofibrant diagrams are objectwise cofibrant. Consequently both endpoints of every augmentation map p^n are cofibrant, since X is cofibrant by hypothesis. Naturality p^n S(theta)=p^m and two-out-of-three give weak equivalences for every structure map, including degeneracies, not merely face maps. Step 2 therefore applies to all of them. I did not assume T preserves weak equivalences with arbitrary endpoints.

For step 4 I read the Reedy lifting axioms and objectwise weak-equivalence characterization in that same cited node, and checked the square against Hovey Lemma 5.5.1 online. The initial diagram is initial componentwise. The left arrow is a Reedy cofibration by step 1, and the right arrow is a Reedy trivial fibration by the item's explicit hypothesis; objectwise trivial fibrancy alone is not substituted. The lower map is T(p), and the square commutes by initiality. The lift is therefore a natural transformation and satisfies the exact requested equation. In degree zero p'^0=1 and T(p^0)=1 force a^0=1. Finally p'^n and T(p^n) are weak equivalences and their equation gives the weak-equivalence components of a. No fibrancy of the constant TX diagram is required.

Small-case checks included n=0 (empty latching diagram), identity structure arrows, constant frames when they happen to satisfy the given Reedy hypotheses, the identity adjunction, and the possibility that X is not fibrant. The argument covers all of these. The conclusion is existential, so neither uniqueness nor naturality in the choice of frame is silently added. Reedy cofibrancy of S' is an available hypothesis, although this lift only requires its stated Reedy trivial fibration to the constant diagram.

I read every hit from the five new prescribed Mathlib searches. The first wording found cofibrant replacements and localizer morphisms; the second wording found ground-model lifting and path objects. The grep found BrownLemma.lean and Reedy/Basic.lean; the latter explicitly lists construction of the Reedy diagram model structure as TODO. None is an attachment or a one-line Mathlib specialization of this whole item. Existing search records were retained, and newly run queries and result digests were appended exactly. No search was invented or recorded as absent when unavailable.

The three dependencies are existing unmerged nodes. The Brown leaf and Reedy theorem are in the item's unit; colimit preservation is a Mathlib leaf, so no off-route tool declaration is needed. No new dependency points to the item. The blueprint same_as search result is empty and the specific inherited from.place is retained.

## Unfinished work

No mathematical part of this item remains. The existing Reedy theorem remains its own dependency, rather than being reproved here. Required server dry run and direct push are recorded below after execution.
