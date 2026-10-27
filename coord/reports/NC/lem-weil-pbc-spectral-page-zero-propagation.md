# Stage-1 report: lem-weil-pbc-spectral-page-zero-propagation

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-spectral-page-zero-propagation.json: statement, now split; no exact Mathlib match for arbitrary integer bidegrees and arbitrary starting page. The statement, statement dependencies, creation stamp, and inherited searches are retained.
- citations.json: verbatim statement excerpts for both citations in Step 1.
- report.md and searches.jsonl: this report and the actual logged Mathlib searches.

There are zero new nodes and zero new Mathlib leaves. The proof reuses the existing Mathlib leaf lem-weil-pbc-short-complex-zero-homology.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for spectral/zero, page/isZero, and isZero/page. CategoryTheory.SpectralSequence.isZero_page_of_isZero_page_two in WeilConjectures/CategoryTheory/SpectralSequence/Vanishing.lean:40 has a sorry-free displayed proof but takes E₂CohomologicalSpectralSequenceNat and a bidegree in natural numbers, and starts at page two. It does not state the item's arbitrary integer-bigraded propagation from any s. The private mapped_page_isZero in Topology/Sheaves/LerayAcyclicComparison.lean:59 is also for natural bidegrees and positive rows. Neither supplies every clause under this item's hypotheses. No exact attachment is claimed.

## WANTED

None. Both Stacks source passages and the current blueprint were available locally.

## Problems found and changes

No statement dispute or source error. The live item was statement-only and the sandbox had no prior item or report. Its source already identifies the correct hint in Stacks Tag 0BDV. I supplied the omitted successor calculation and the full induction rather than moving propagation to another node. No target, definition, coefficient category, or unit route changes.

The latest blueprint is literature/blueprint/latest/blueprint/sec-proper-base-change/sk-lem-pbc-composition-cancellation/lemma-weil-pbc-cancellation.proof.md. Part (1) says that the Grothendieck spectral sequence collapses to row q=0. This item supplies persistence of the vanishing, strictly before any edge-map or abutment argument. I also read dag/units/sk-thm-reduction.json and dag/chapters/sec-proper-base-change.json; no changes are needed to either. The older coord/brief-stage1.md refers to coord/dag-sync.md, which is absent in this read clone; the direct brief's live-repository and latest-blueprint instructions were followed.

## Searches and reuse

The whole DAG was searched by statements and by homology/zero, zero-entry, short-complex, middle-object, and the exact Mathlib declaration. This found lem-weil-pbc-short-complex-zero-homology, whose first assertion is exactly the successor calculation's input. Creating a new node for it would duplicate an existing, more general leaf. Blueprint searches for homology zero, zero entry, homology vanishes, and spectral sequence zero found no exact alternate blueprint statement for the item. The ancestor command confirms lemma-weil-pbc-cancellation, through lem-weil-pbc-first-quadrant-row-collapse, and its exact proof place was retained.

All new Mathlib queries were run through msearch.py and their results read. The first semantic propagation query returned total-complex differentials and double-complex facts. The second phrasing, in terms of support of later pages, returned support predicates of a single complex and cochain-complex bounds; none states page propagation. Loogle with CategoryTheory.SpectralSequence and CategoryTheory.Limits.IsZero returned no hits. Grep in Algebra/Homology found the short-complex homology lemma and spectral-object-specific vanishing statements; grep of Algebra/Homology/SpectralSequence for isZero, vanish, or support returned no hits. LeanSearch returned zero-map and differential facts, with no page-propagation theorem. Targeted LeanFinder and Loogle searches both confirmed CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂; these queries reinforce reuse of the existing leaf rather than justify a new node. All services used here answered; the inherited unavailable search records remain unchanged as history.

I read Mathlib/Algebra/Homology/ShortComplex/Homology.lean:1147, which states IsZero S.X₂ implies IsZero S.homology assuming homology exists, and SpectralSequence/Basic.lean:37-45, whose page and iso fields supply exactly the page complex and next-page isomorphism. The existing leaf is already stated for abelian categories, so no extra homology-existence hypothesis is imported into this item. The spectral-object results read in SpectralObject/SpectralSequence.lean:520-543 require spectral-object presentation data and vanishing of its H objects; they are not one-line instances of the present hypotheses.

## Not duplicates

No new nodes. The existing short-complex leaf is reused rather than restated.

## Review by NC

I read Stacks homology.tex at definition-spectral-sequence (Tag 011N), including its explicit permission to begin at an arbitrary page and use specified isomorphisms, and lemma-relate-boundedness (Tag 0BDV), whose proof hint is precisely persistence of a zero entry. I checked the tag-to-label mapping in literature/stacks-project/tags/tags. This is the source route of the item, with the hint expanded into an argument.

In Step 1 I opened and read both cited node statements. def-sp-spectral-sequence supplies complexes on every page and homology isomorphisms to the next page, for arbitrary index set and starting page. At index (p,q), the incoming term must be (p-t,q+t-1), and the outgoing term (p+t,q-t+1); these are the terms actually written in the proof. Their composite is zero by the page-complex condition. The statement of lem-weil-pbc-short-complex-zero-homology explicitly says that a short complex with zero middle object has zero homology. It applies because the ambient category is abelian and the middle object is exactly the hypothesized zero entry. Nothing is taken from the other two clauses of this leaf. Finally I wrote out the bijections on Hom sets under the specified page isomorphism, so transfer of the zero-object property is explicit. The two corresponding citations.json quotes are literal substrings of those node statements.

Step 2 uses the successor conclusion established in Step 1, with the inductive claim stated at s+k, base k=0, and t=s+k in the successor. The inequality t>=2 follows from s>=2 and k>=0. Expressing r-s as a natural number is justified by r>=s. This is elementary induction and arithmetic, not an unquoted spectral-sequence theorem. Step 3 uses Step 2 with s=2 and splits the support condition into p<0 or q<0, and the remaining q>0 case. An eventually stationary positive-row term is represented by a late page, all of whose entries in that row have already been shown zero; no convergence, exact couple, abutment, or identification with a cohomology object is asserted.

I tested the boundary r=s (the hypothesis itself), the successor r=s+1, s>2, negative p and negative q, q=0 with p<0, and q>0 with arbitrary p. At p>=0,q=0 no vanishing is claimed. The trivial spectral sequence and the zero abelian category satisfy all clauses. None of the proof needs first-quadrant hypotheses until Step 3. An entry killed on a later page need not have been zero earlier, and no converse is used. There is no infinite-limit argument: the last clause concerns a stationary value only.

Against delivery-errors B-E, no new node, hidden proof sketch, relabelled clause, new definition, or duplicate was introduced. Every non-elementary input is a cited existing node, and the exact cited statements were checked above (C1/C4). The proof has no circular citation and uses no other-unit theorem as a route replacement: the only theorem input is an existing Mathlib leaf. All three steps are under 2000 characters and the assembly proof is under 3000 characters. The non-elementary step is the local homology calculation, expressly marked non-elementary; the induction and support case split are expressly elementary. No SGA source is cited. No Lean was written and no compiler or build tool was run.

## Unfinished work

No mathematical work remains for this split. Delivery requires the dry-run preflight and push specified in the brief.
